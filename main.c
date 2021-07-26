#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <memory.h>
#include <stdint.h>
#include <inttypes.h>
#include <sys/types.h>
#include <sys/queue.h>
#include <netinet/in.h>
#include <setjmp.h>
#include <stdarg.h>
#include <ctype.h>
#include <errno.h>
#include <getopt.h>
#include <signal.h>
#include <stdbool.h>
#include <rte_common.h>
#include <rte_log.h>
#include <rte_malloc.h>
#include <rte_memory.h>
#include <rte_memcpy.h>
#include <rte_memzone.h>
#include <rte_eal.h>
#include <rte_per_lcore.h>
#include <rte_launch.h>
#include <rte_atomic.h>
#include <rte_cycles.h>
#include <rte_prefetch.h>
#include <rte_lcore.h>
#include <rte_per_lcore.h>
#include <rte_branch_prediction.h>
#include <rte_interrupts.h>
#include <rte_pci.h>
#include <rte_random.h>
#include <rte_debug.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_ring.h>
#include <rte_mempool.h>
#include <rte_mbuf.h>
#include <rte_errno.h>
#include <rte_timer.h>
#include <rte_mbuf_ptype.h>
#include <rte_byteorder.h>
#include <rte_ip.h>
#include <rte_tcp.h>
#include <rte_udp.h>
#include <rte_gre.h>
#include <rte_sctp.h>
#include <rte_flow.h>
#include <rte_net.h>
static int64_t loss_random(const char *loss_rate);
static int64_t loss_random_a(double loss_rate);
static bool loss_event(void);
static bool loss_event_random(uint64_t loss_rate);
static bool loss_event_GE(uint64_t loss_rate_n, uint64_t loss_rate_a, uint64_t st_ch_rate_no2ab, uint64_t st_ch_rate_ab2no);
static bool loss_event_4state( uint64_t p13, uint64_t p14, uint64_t p23, uint64_t p31, uint64_t p32);
static bool dup_event(void);
#define RANDOM_MAX 1000000000
#define J 128
static volatile bool force_quit;
#define RTE_LOGTYPE_DEMU RTE_LOGTYPE_USER1
#define RTE_TEST_RX_DESC_DEFAULT 128
#define RTE_TEST_TX_DESC_DEFAULT 512
static uint16_t nb_rxd = RTE_TEST_RX_DESC_DEFAULT;
static uint16_t nb_txd = RTE_TEST_TX_DESC_DEFAULT;
/* ethernet addresses of ports */
static struct ether_addr demu_ports_eth_addr[RTE_MAX_ETHPORTS];
struct rte_mempool * demu_pktmbuf_pool = NULL;
static uint32_t demu_enabled_port_mask = 0;
/* Per-port statistics struct */
struct demu_port_statistics {
	uint64_t tx;
	uint64_t rx;
	uint64_t dropped;
	uint64_t rx_worker_dropped;
	uint64_t worker_tx_dropped;
	uint64_t queue_dropped;
	uint64_t discarded;
} __rte_cache_aligned;
struct demu_port_statistics port_statistics[RTE_MAX_ETHPORTS];
/*
 * Assigment of each thread to a specific CPU core.
 * Currently, each of two threads is running for rx, tx, worker threads.
 */
#define RX_THREAD_CORE 2
#define RX_THREAD_CORE2 3
#define TX_THREAD_CORE 4
#define TX_THREAD_CORE2 5
#define WORKER_THREAD_CORE 6
#define WORKER_THREAD_CORE2 7
#define TIMER_THREAD_CORE 8
/*
 * The maximum number of packets which are processed in burst.
 * Note: do not set PKT_BURST_RX to 1.
 */
#define PKT_BURST_RX 32
#define PKT_BURST_TX 32
#define PKT_BURST_WORKER 32
/*
 * The default mempool size is not enough for bufferijng 64KB of short packets for 1 second.
 * SHORT_PACKET should be enabled in the case of short packet benchmarking.
 * #define SHORT_PACKET
 */
#ifdef SHORT_PACKET
#define DEMU_DELAYED_BUFFER_PKTS 8388608/J
#define MEMPOOL_BUF_SIZE 1152
#else
#define DEMU_DELAYED_BUFFER_PKTS 4194304/J
#define MEMPOOL_BUF_SIZE 2048 /* 2048 */
#endif
#define MEMPOOL_CACHE_SIZE 512
#define DEMU_SEND_BUFFER_SIZE_PKTS 512
struct rte_ring *rx_to_workers;
struct rte_ring *rx_to_workers2;
struct rte_ring *workers_to_tx;
// struct rte_ring *workers_to_tx2;
struct rte_ring *rx_to_workers_arr[17];
struct rte_ring *header_pointers;
static uint64_t delayed_time = 0;
// 测试 flow director
static uint8_t selected_queue = 1;
#define SRC_IP ((0<<24) + (0<<16) + (0<<8) + 0)       /* src ip = 0.0.0.0 */
#define DEST_IP1 ((192<<24) + (168<<16) + (1<<8) + 1)  /* dest ip = 192.168.1.1 */
#define FULL_MASK 0xffffffff                          /* full mask */
#define EMPTY_MASK 0x0                                /* empty mask */
#define MAX_PATTERN_NUM     4
#define DEST_IP2 ((192<<24) + (168<<16) + (1<<8) + 2)
#define DEST_IP3 ((192<<24) + (168<<16) + (1<<8) + 3)
#define DEST_IP4 ((192<<24) + (168<<16) + (1<<8) + 4)
#define DEST_IP5 ((192<<24) + (168<<16) + (1<<8) + 5)

enum demu_loss_mode {
	LOSS_MODE_NONE,
	LOSS_MODE_RANDOM,
	LOSS_MODE_GE,
	LOSS_MODE_4STATE,
};
static enum demu_loss_mode loss_mode = LOSS_MODE_NONE;

static uint64_t loss_percent_1 = 0;
static uint64_t loss_percent_2 = 0;
// static uint64_t change_percent_1 = 0;
// static uint64_t change_percent_2 = 0;

static uint64_t dup_rate = 0;

static const struct rte_eth_conf port_conf = {
	.rxmode = {
		.split_hdr_size = 0,
		.header_split   = 0, /**< Header Split disabled */
		.hw_ip_checksum = 0, /**< IP checksum offload disabled */
		.hw_vlan_filter = 0, /**< VLAN filtering disabled */
		.jumbo_frame    = 0, /**< Jumbo Frame Support disabled */
		.hw_strip_crc   = 0, /**< CRC stripped by hardware */
	},
	.txmode = {
		.mq_mode = ETH_MQ_TX_NONE,
	},
};

static struct rte_eth_rxconf rx_conf = {
	.rx_thresh = {                    /**< RX ring threshold registers. */
		.pthresh = 8,             /**< Ring prefetch threshold. */
		.hthresh = 8,             /**< Ring host threshold. */
		.wthresh = 0,             /**< Ring writeback threshold. */
	},
	.rx_free_thresh = 32,             /**< Drives the freeing of RX descriptors. */
	.rx_drop_en = 0,                  /**< Drop packets if no descriptors are available. */
	.rx_deferred_start = 0,           /**< Do not start queue with rte_eth_dev_start(). */
};

static struct rte_eth_txconf tx_conf = {
	.tx_thresh = {                    /**< TX ring threshold registers. */
		.pthresh = 32,
		.hthresh = 0,
		.wthresh = 0,
	},
	.tx_rs_thresh = 32,               /**< Drives the setting of RS bit on TXDs. */
	.tx_free_thresh = 32,             /**< Start freeing TX buffers if there are less free descriptors than this value. */
	.txq_flags = (ETH_TXQ_FLAGS_NOMULTSEGS |
			ETH_TXQ_FLAGS_NOVLANOFFL |
			ETH_TXQ_FLAGS_NOXSUMSCTP |
			ETH_TXQ_FLAGS_NOXSUMUDP |
			ETH_TXQ_FLAGS_NOXSUMTCP),
	.tx_deferred_start = 0,            /**< Do not start queue with rte_eth_dev_start(). */
};

/* #define DEBUG_RX */
/* #define DEBUG_TX */

// #define TIME_RECORD_BUF_SIZE 10000
// double time_record [TIME_RECORD_BUF_SIZE] ={0};
uint64_t packet_cnt = 0;
int check_num = 10000;
int queue_num = 2;// 分流队列数量

#ifdef DEBUG_RX
#define RX_STAT_BUF_SIZE 30000/J
double rx_stat[RX_STAT_BUF_SIZE] = {0};
uint64_t rx_cnt = 0;
#endif

#ifdef DEBUG_TX
#define TX_STAT_BUF_SIZE 30000/J
double tx_stat[TX_STAT_BUF_SIZE] = {0};
uint64_t tx_cnt = 0;
#endif

static int ss_parser_pkt_ipv4(struct rte_mbuf *m, uint32_t off_len)
{
    // uint16_t proto;
    uint32_t off = off_len;
    struct ipv4_hdr ip4h_copy;
    const struct ipv4_hdr *ip4h;

    ip4h = rte_pktmbuf_read(m, off, sizeof(*ip4h), &ip4h_copy);
    //SS_RETURN_RES(unlikely(ip4h == NULL), 0);
    //SS_RETURN_RES(ip4h->fragment_offset & rte_cpu_to_be_16(
        //IPV4_HDR_OFFSET_MASK | IPV4_HDR_MF_FLAG), 0);

    //m->ss.packet_type |= ss_ptype_l3_ipv4(ip4h->version_ihl);
    //m->ss.sip[0] = ip4h->src_addr;
    //m->ss.dip[0] = ip4h->dst_addr;

	printf("ip-----------");
	// RTE_LOG(INFO,DEMU,"%" PRIu32" ,ip4h->src_addr);
		printf("%" PRIu32"\n",ip4h->src_addr );
	// RTE_LOG(INFO,DEMU,"%" PRIu32" ,ip4h->src_addr);
	// RTE_LOG(INFO,DEMU,"%" PRIu32" ,ip4h->dst_addr);

    //m->ss.l3_len = SS_IPV4_HLEN(ip4h);
    //off += m->ss.l3_len;
    //proto = ip4h->next_proto_id;
    //m->ss.packet_type |= ss_ptype_l4(proto);

    //return ss_parser_pkt_l4_proto(m, proto, off);
	return 0;
}


static int ss_parser_pkt_ether(struct rte_mbuf *m)
{
    int ret = 0;
    uint32_t off = 0;
    struct ether_hdr eh_copy;
    const struct ether_hdr *eh;

    eh = rte_pktmbuf_read(m, off, sizeof(*eh), &eh_copy);
    //SS_RETURN_RES(unlikely(eh == NULL), 0);

    // rte_memcpy(m->ss.smac, eh->s_addr.addr_bytes, ETHER_ADDR_LEN);
    // rte_memcpy(m->ss.dmac, eh->d_addr.addr_bytes, ETHER_ADDR_LEN);
    // m->ss.packet_type = RTE_PTYPE_L2_ETHER;
    // m->ss.l2_len = sizeof(*eh);
    off = sizeof(*eh);

    switch (rte_be_to_cpu_16(eh->ether_type)) {
    case ETHER_TYPE_IPv4: //IPv4
    {
        ret = ss_parser_pkt_ipv4(m, off);
        break;
	}
	default :
		break;
	}
	return ret;
}



static int ss_parser_pkt(struct rte_mbuf *m)
{
    //SS_RETURN_RES(unlikely(m == NULL), 0);
    // memset(&m->ss, 0, sizeof(struct ss_mbuf));

    return ss_parser_pkt_ether(m);
}

static inline void
pktmbuf_free_bulk(struct rte_mbuf *mbuf_table[], unsigned n)
{
	unsigned int i;

	for (i = 0; i < n; i++)
		rte_pktmbuf_free(mbuf_table[i]);
}

static double max_speed = 10000000000.0; /* FIXME: 10Gbps */
static uint64_t limit_speed = 0;
static uint64_t amount_token = 0; /* one token represents capacity of 1 Mbps. */
static uint64_t sub_amount_token = 0;

static uint64_t limit_speed2 = 500000000.0; //500m
static uint64_t amount_token2 = 0; /* one token represents capacity of 1 Mbps. */
static uint64_t sub_amount_token2 = 0;

static uint64_t limit_speed3 = 1000000000.0; //1G
static uint64_t amount_token3 = 0; /* one token represents capacity of 1 Mbps. */
static uint64_t sub_amount_token3 = 0;

static uint64_t limit_speed4 = 2000000000.0; //2G
static uint64_t amount_token4 = 0; /* one token represents capacity of 1 Mbps. */
static uint64_t sub_amount_token4 = 0;

static void
tx_timer_cb(__attribute__((unused)) struct rte_timer *tmpTime, __attribute__((unused)) void *arg)
{
	double upper_limit_speed = max_speed / 100000;

	if (amount_token >= (uint64_t)upper_limit_speed)
		return;

	if (limit_speed >= 1000000)
		amount_token += (limit_speed / 1000000);
	else {
		sub_amount_token += limit_speed;
		if (sub_amount_token > 1000000) {
			amount_token += sub_amount_token / 1000000;
			sub_amount_token %= 1000000;
		}
	}

	if (amount_token2 >= (uint64_t)upper_limit_speed)
		return;

	if (limit_speed2 >= 1000000)
		amount_token2 += (limit_speed2 / 1000000);
	else {
		sub_amount_token2 += limit_speed2;
		if (sub_amount_token2 > 1000000) {
			amount_token2 += sub_amount_token2 / 1000000;
			sub_amount_token2 %= 1000000;
		}
	}

	if (amount_token3 >= (uint64_t)upper_limit_speed)
		return;

	if (limit_speed3 >= 1000000)
		amount_token3 += (limit_speed3 / 1000000);
	else {
		sub_amount_token3 += limit_speed3;
		if (sub_amount_token3 > 1000000) {
			amount_token3 += sub_amount_token3 / 1000000;
			sub_amount_token3 %= 1000000;
		}
	}

	if (amount_token4 >= (uint64_t)upper_limit_speed)
		return;

	if (limit_speed4 >= 1000000)
		amount_token4 += (limit_speed4 / 1000000);
	else {
		sub_amount_token4 += limit_speed4;
		if (sub_amount_token4 > 1000000) {
			amount_token4 += sub_amount_token4 / 1000000;
			sub_amount_token4 %= 1000000;
		}
	}
}

static void
demu_timer_loop(void)
{
	unsigned lcore_id;
	uint64_t hz;
	struct rte_timer timer;

	lcore_id = rte_lcore_id();
	hz = rte_get_timer_hz();

	rte_timer_init(&timer);
	rte_timer_reset(&timer, hz / 1000000, PERIODICAL, lcore_id, tx_timer_cb, NULL);



	RTE_LOG(INFO, DEMU, "Entering timer loop on lcore %u\n", lcore_id);
	RTE_LOG(INFO, DEMU, "  Linit speed is %lu bps\n", limit_speed);

	while (!force_quit)
		rte_timer_manage();
}

static void
demu_tx_loop(unsigned portid)
{
	struct rte_mbuf *send_buf[PKT_BURST_TX];
	// struct rte_ring **cring;
	unsigned lcore_id;
	uint32_t numdeq = 0;
	uint16_t sent;

	lcore_id = rte_lcore_id();
	// unsigned count=0;
	RTE_LOG(INFO, DEMU, "Entering main tx loop on lcore %u portid %u\n", lcore_id, portid);

	while (!force_quit) {
		// if (portid == 0)
		// 	cring = &workers_to_tx;
		// else
		// 	cring = &workers_to_tx;

		numdeq = rte_ring_mc_dequeue_burst(workers_to_tx,
				(void *)send_buf, PKT_BURST_TX, NULL);

		if (unlikely(numdeq == 0))
			continue;

		sent = 0;
		// count+=numdeq;
		// if(count>700){
		// 	RTE_LOG(INFO, DEMU, "tx >700");
		// 	break;
		// }
		while (numdeq > sent)
			sent += rte_eth_tx_burst(portid, 0, send_buf + sent, numdeq - sent);

#ifdef DEBUG_TX
		if (tx_cnt < TX_STAT_BUF_SIZE) {
			for (uint32_t i = 0; i < numdeq; i++) {
				tx_stat[tx_cnt] = rte_rdtsc();
				tx_cnt++;
			}
		}
#endif
	}
	// RTE_LOG(INFO, DEMU, "tx count = %u",count);
}

struct rte_flow *generate_ipv4_flow(uint16_t port_id, uint16_t rx_q, uint32_t src_ip, uint32_t src_mask,
        uint32_t dest_ip, uint32_t dest_mask, struct rte_flow_error *error)
{
    struct rte_flow_attr attr;                      // 流的 attr
    struct rte_flow_item pattern[MAX_PATTERN_NUM];  // 流的 pattern。关于 item，见：http://doc.dpdk.org/api/structrte__flow__item.html
    struct rte_flow_action action[MAX_PATTERN_NUM]; // 流的 action ， 这三个是创建一个流的关键。
    struct rte_flow *flow = NULL;
    struct rte_flow_action_queue queue = { .index = rx_q };
    struct rte_flow_item_eth eth_spec; // spec 和
    struct rte_flow_item_eth eth_mask; // mask 是 item 的另外两个字段。void * ，但需要设置成和你选定的特定 type 一样。
    struct rte_flow_item_vlan vlan_spec;
    struct rte_flow_item_vlan vlan_mask;
    struct rte_flow_item_ipv4 ip_spec;
    struct rte_flow_item_ipv4 ip_mask;

    struct rte_flow_item_ipv4 ip_spec2;
    struct rte_flow_item_ipv4 ip_mask2;

    struct rte_flow_item_ipv4 ip_spec3;
    struct rte_flow_item_ipv4 ip_mask3;

    struct rte_flow_item_ipv4 ip_spec4;
    struct rte_flow_item_ipv4 ip_mask4;

    int res;
 
    memset(pattern, 0, sizeof(pattern));
    memset(action, 0, sizeof(action));

    memset(&attr, 0, sizeof(struct rte_flow_attr));
    attr.ingress = 1; // 意思是只对入口流量生效的属性

 
    action[0].type = RTE_FLOW_ACTION_TYPE_QUEUE; // 动作是：Assigns packets to a given queue index.
    action[0].conf = &queue;
    action[1].type = RTE_FLOW_ACTION_TYPE_END; // 动作数组必须用 RTE_FLOW_ACTION_TYPE_END 作为最后一个元素来结尾
    memset(&ip_spec, 0, sizeof(struct rte_flow_item_ipv4));
    memset(&ip_mask, 0, sizeof(struct rte_flow_item_ipv4));

    ip_spec.hdr.dst_addr = htonl(dest_ip); // 将主机数转换成无符号长整型的网络字节顺序
    ip_mask.hdr.dst_addr = dest_mask;
    ip_spec.hdr.src_addr = htonl(src_ip);
    ip_mask.hdr.src_addr = src_mask;

    pattern[0].type = RTE_FLOW_ITEM_TYPE_IPV4;
    pattern[0].spec = &ip_spec;
    pattern[0].mask = &ip_mask;

    memset(&ip_spec2, 0, sizeof(struct rte_flow_item_ipv4));
    memset(&ip_mask2, 0, sizeof(struct rte_flow_item_ipv4));

    ip_spec2.hdr.dst_addr = htonl(DEST_IP2); // 将主机数转换成无符号长整型的网络字节顺序
    ip_mask2.hdr.dst_addr = dest_mask;
    ip_spec2.hdr.src_addr = htonl(src_ip);
    ip_mask2.hdr.src_addr = src_mask;

    // pattern[1].type = RTE_FLOW_ITEM_TYPE_IPV4;
    // pattern[1].spec = &ip_spec2;
    // pattern[1].mask = &ip_mask2;

    // pattern[0].type = RTE_FLOW_ITEM_TYPE_IPV4;
    // pattern[0].spec = &ip_spec;
    // pattern[0].mask = &ip_mask;

    // pattern[0].type = RTE_FLOW_ITEM_TYPE_IPV4;
    // pattern[0].spec = &ip_spec;
    // pattern[0].mask = &ip_mask;
    pattern[1].type = RTE_FLOW_ITEM_TYPE_END;

    // 验证这条流的有效性
    res = rte_flow_validate(port_id, &attr, pattern, action, error);
    if (!res)
        flow = rte_flow_create(port_id, &attr, pattern, action, error);
    return flow;
}

// 验证端口确实能用作过滤器
// struct rte_flow *generate_ipv4_flow(uint16_t port_id, uint16_t rx_q, uint32_t src_ip, uint32_t src_mask,
//         uint32_t dest_ip, uint32_t dest_mask, struct rte_flow_error *error)
// {
//     struct rte_flow_attr attr;                      // 流的 attr
//     struct rte_flow_item pattern[MAX_PATTERN_NUM];  // 流的 pattern。关于 item，见：http://doc.dpdk.org/api/structrte__flow__item.html
//     struct rte_flow_action action[MAX_PATTERN_NUM]; // 流的 action ， 这三个是创建一个流的关键。
//     struct rte_flow *flow = NULL;
//     struct rte_flow_action_queue queue = { .index = rx_q };
//     struct rte_flow_item_eth eth_spec; // spec 和
//     struct rte_flow_item_eth eth_mask; // mask 是 item 的另外两个字段。void * ，但需要设置成和你选定的特定 type 一样。
//     struct rte_flow_item_vlan vlan_spec;
//     struct rte_flow_item_vlan vlan_mask;
//     struct rte_flow_item_ipv4 ip_spec;
//     struct rte_flow_item_ipv4 ip_mask;

//     struct rte_flow_item_ipv4 ip_spec2;
//     struct rte_flow_item_ipv4 ip_mask2;

//     struct rte_flow_item_ipv4 ip_spec3;
//     struct rte_flow_item_ipv4 ip_mask3;

//     struct rte_flow_item_ipv4 ip_spec4;
//     struct rte_flow_item_ipv4 ip_mask4;

//     struct rte_flow_item_udp udp_s_port_spec;
//     struct rte_flow_item_udp udp_s_port_mask;

//     int res;
 
//     memset(pattern, 0, sizeof(pattern));
//     memset(action, 0, sizeof(action));

//     memset(&attr, 0, sizeof(struct rte_flow_attr));
//     attr.ingress = 1; // 意思是只对入口流量生效的属性

 
//     action[0].type = RTE_FLOW_ACTION_TYPE_QUEUE; // 动作是：Assigns packets to a given queue index.
//     action[0].conf = &queue;
//     action[1].type = RTE_FLOW_ACTION_TYPE_END; // 动作数组必须用 RTE_FLOW_ACTION_TYPE_END 作为最后一个元素来结尾
    

//     memset(&ip_spec, 0, sizeof(struct rte_flow_item_ipv4));
//     memset(&ip_mask, 0, sizeof(struct rte_flow_item_ipv4));

//     ip_spec.hdr.dst_addr = htonl(dest_ip); // 将主机数转换成无符号长整型的网络字节顺序
//     ip_mask.hdr.dst_addr = dest_mask;
//     ip_spec.hdr.src_addr = htonl(src_ip);
//     ip_mask.hdr.src_addr = src_mask;

//     pattern[0].type = RTE_FLOW_ITEM_TYPE_IPV4;
//     pattern[0].spec = &ip_spec;
//     pattern[0].mask = &ip_mask;

//     memset(&udp_s_port_spec, 0, sizeof(struct rte_flow_item_udp));
//     memset(&udp_s_port_mask, 0, sizeof(struct rte_flow_item_udp));

//     udp_s_port_spec.hdr.src_port= rte_cpu_to_be_16(1);
//     udp_s_port_spec.hdr.dst_port= 1024;

//     udp_s_port_mask.hdr.src_port= 0xffff;
//     udp_s_port_mask.hdr.dst_port= EMPTY_MASK;

//     pattern[1].type = RTE_FLOW_ITEM_TYPE_UDP;
//     pattern[1].spec = &udp_s_port_spec;

//     pattern[1].mask = &udp_s_port_mask;

//     pattern[2].type = RTE_FLOW_ITEM_TYPE_END;

//     // 验证这条流的有效性
//     res = rte_flow_validate(port_id, &attr, pattern, action, error);
//     if (!res)
//         flow = rte_flow_create(port_id, &attr, pattern, action, error);
//     return flow;
// }

static void
demu_rx_loop(unsigned portid)
{
	// struct rte_mbuf *pkts_burst[PKT_BURST_RX *queue_num];
	int pkts_burst_length;
	if(PKT_BURST_RX *queue_num>128)
		pkts_burst_length = 128;
	else pkts_burst_length = PKT_BURST_RX *queue_num;
	struct rte_mbuf *pkts_burst[pkts_burst_length];
	unsigned lcore_id;

	unsigned nb_rx, i;
	unsigned nb_loss;
	unsigned nb_dup;
	uint32_t numenq;

	lcore_id = rte_lcore_id();

	RTE_LOG(INFO, DEMU, "Entering main rx loop on lcore %u portid %u\n", lcore_id, portid);
    // 多个 buf
    struct rte_mbuf * rx2w_buffer_arr[queue_num][PKT_BURST_RX];
    // 每个buf 的实际长度root
    // int buf_len[queue_num] = {0};
    int *buf_len;
    buf_len = (int*)malloc(queue_num*(sizeof(int)));
    memset(buf_len, 0, queue_num);
    unsigned count=0;
    int queue_id=0;
    int queue_i =0;
    int count_in_ring =0;
    int add_head_ring_fail=0;
    int add_ring_not_full =0;
    int count_add_headpoint=0;
    // int num_ring_in_headerpoint=0;
    int nb_rx_i=0;
    int arr_len =900;
    int a[arr_len];
    for(int k=0;k<arr_len;k++){
    	a[k]= -1;
	}
	unsigned target = queue_num *8;

	// 网卡时间戳
	    /* Enable timesync timestamping for the Ethernet device */
    // retval = rte_eth_timesync_enable(portid);
    // if (retval < 0) {
    //     printf("Timesync enable failed: %d\n", retval);
    //     return retval;
    // }


	while (!force_quit) {
		// nb_rx = rte_eth_rx_burst((uint8_t) port id , 0, pkts_burst, PKT_BURST_RX);
		// nb_rx = rte_eth_rx_burst((uint8_t) portid, 0, pkts_burst, PKT_BURST_RX*queue_num);
		nb_rx = rte_eth_rx_burst((uint8_t) portid, 0, pkts_burst, pkts_burst_length);// 因为最大也就127
		
		if (likely(nb_rx == 0))
			continue;


		if(nb_rx_i <arr_len){
			a[nb_rx_i] = nb_rx;
			nb_rx_i++;
			// printf("nb_rx =%d\n",nb_rx );
		}

		for(int j=0;j<queue_num;j++) 
			buf_len[j]=0;
		// for (i = 0; i < nb_rx; i++) {
		for (i = 0; i < nb_rx; i++) {
			// struct rte_mbuf *clone;

//			if (portid == 0 && loss_event()) {
//				port_statistics[portid].discarded++;
//				nb_loss++;
//				continue;
//			}
            // int queue_id = i%queue_num;
            queue_id =( count &(queue_num-1));

            rx2w_buffer_arr[queue_id][buf_len[queue_id]] = pkts_burst[i];
            //rte_prefetch0(rte_pktmbuf_mtod(rx2w_buffer_arr[queue_id][buf_len[queue_id]], void *)); //引起 segment fault，先注释掉
            rx2w_buffer_arr[queue_id][buf_len[queue_id]]->udata64 = rte_rdtsc();
            buf_len[queue_id] ++;
            
            count++;
            // ip解析
			//int resa = ss_parser_pkt(pkts_burst[i]);

			/* FIXME: we do not check the buffer overrun of rx2w_buffer. */
//			if (portid == 0 && dup_event()) {
//				clone = rte_pktmbuf_clone(rx2w_buffer[i - nb_loss + nb_dup], demu_pktmbuf_pool);
//				if (clone == NULL)
//					RTE_LOG(ERR, DEMU, "cannot clone a packet\n");
//				nb_dup++;
//				rx2w_buffer[i - nb_loss + nb_dup] = clone;
//			}

#ifdef DEBUG_RX
			if (rx_cnt < RX_STAT_BUF_SIZE) {
				rx_stat[rx_cnt] = rte_rdtsc();
				rx_cnt++;
			}
#endif
		}
		// 将数据分发到多个队列中 rx_to_workers_arr 【】
		for(queue_i =0 ;queue_i< queue_num;queue_i++){
			if(buf_len[queue_i]>0){
				//ring 为空，则填上数据后，加入头指针队列，否则不加入头指针队列

				// if(rte_ring_count(rx_to_workers_arr[queue_i])<64){ // 加入头指针队列
				// 	numenq = rte_ring_sp_enqueue_burst(rx_to_workers_arr[queue_i],
    //                 (void *)rx2w_buffer_arr[queue_i], buf_len[queue_i], NULL);
				// 	if(numenq != buf_len[queue_i]){ //后续可以删掉这个，优化性能
				// 		RTE_LOG(INFO, DEMU, "numenq != ip1");
				// 	}
				// 	numenq = rte_ring_sp_enqueue(header_pointers, &rx_to_workers_arr[queue_i]);
				// 	if (numenq != 0){}//RTE_LOG(INFO, DEMU, "head-pointer add fail %d\n",i);}
				// 	// num_ring_in_headerpoint++;
				// 	// printf("num_ring_in_headerpoint =%d\n",num_ring_in_headerpoint );
				// }else{
				// 	numenq = rte_ring_sp_enqueue_burst(rx_to_workers_arr[queue_i],
    //                 (void *)rx2w_buffer_arr[queue_i], buf_len[queue_i], NULL);
				// 	if(numenq != buf_len[queue_i]){ //后续可以删掉这个，优化性能
				// 		RTE_LOG(INFO, DEMU, "numenq != ip1");
				// 	}	
				// }
				numenq = rte_ring_sp_enqueue_burst(rx_to_workers_arr[queue_i],
                    (void *)rx2w_buffer_arr[queue_i], buf_len[queue_i], NULL);
				count_add_headpoint++;
				numenq = rte_ring_sp_enqueue(header_pointers, &rx_to_workers_arr[queue_i]);
				if(numenq!=0) add_head_ring_fail++;			
				// if (numenq != 0){RTE_LOG(INFO, DEMU, "head-pointer add fail %d\n",queue_i);}//RTE_LOG(INFO, DEMU, "head-pointer add fail %d\n",i);}
			}
		}
	}
	printf("add_head_ring_fail=%d\n",add_head_ring_fail );
	// printf("add_ring_not_full=%d\n",add_ring_not_full ); // 始终为0
	printf("count_add_headpoint=%d\n",count_add_headpoint );
	for(int k=0;k<nb_rx_i;k++){
		printf("%d ", a[k]);
	}
	printf("\n");
}

static void
rx_delay_thread(unsigned portid,unsigned queueid,struct rte_ring* ring1,uint64_t *p)
{
    uint32_t numenq;
    uint16_t burst_size = 0;
    uint16_t burst_size_from_nic = 0;
	uint16_t total_size = 0;
	struct rte_mbuf *burst_buffer[32];
	struct rte_mbuf *pkts_burst[32];
	uint64_t diff_tsc;
	uint64_t delay_dif_k =1;
	uint16_t i;
    uint16_t last_size=0;
	unsigned lcore_id;
	int status;
	unsigned count=0;
	lcore_id = rte_lcore_id();
	RTE_LOG(INFO, DEMU, "Entering main worker on lcore %u, portId:%u\n", lcore_id,portid);	
	unsigned count_i=0;
	void ** temp_ring_point;
	unsigned ring_empty_count=0;
    unsigned flag=0;
    unsigned count_rx_num_nic=0;

    unsigned  finished=1;
    unsigned count_break=0;
    unsigned count_to_next=0;
    printf("delayed_time: %"PRIu64"\n", delayed_time);
    i = 0;
	while (!force_quit) {    
        burst_size_from_nic = rte_eth_rx_burst((uint8_t) portid, queueid, pkts_burst, 32);

        if(burst_size_from_nic!=0){
            for (int j  = 0; j <burst_size_from_nic ; j++) {
                pkts_burst[j]->udata64 = rte_rdtsc();
            }
            numenq = rte_ring_sp_enqueue_burst(ring1,
                    (void *)pkts_burst, burst_size_from_nic, NULL);
            count_rx_num_nic += burst_size_from_nic;
        }
        if(finished==0){// 未结束 “把一轮收包的数据包 全部 转发到下一个ring”
                // i=last_size;
        }else {
            burst_size = rte_ring_sc_dequeue_burst(ring1,
                (void *)burst_buffer, 32, NULL);
            count_break+=burst_size;
        }
		while(i != burst_size){
                diff_tsc = rte_rdtsc() - burst_buffer[i]->udata64;
                if (diff_tsc < delayed_time){
                    break;
                }
                if (limit_speed) {
					uint16_t pkt_size_bit = burst_buffer[i]->pkt_len * 8;

					// if (amount_token >= pkt_size_bit)
					// 	amount_token -= pkt_size_bit;
					if (*p >= pkt_size_bit)
						*p -= pkt_size_bit;
					else
						continue;
				}
                do {
                    status = rte_ring_mp_enqueue(workers_to_tx, burst_buffer[i]);
                } while (status == -ENOBUFS);
                i++;
                count_to_next++;
        }
        if(i==burst_size){
            finished=1;
            i=0;
        }else{
            finished=0;
        }
		// while (true) {
		// 	/* Add a given delay when a packet comes from the port 0.
		// 	 * FIXME: fix this implementation.
		// 	 */
  //           if(finished==0){// 未结束 “把一轮收包的数据包 全部 转发到下一个ring”
  //               // i=last_size;
  //           }else {
  //               burst_size = rte_ring_sc_dequeue_burst(ring1,
  //                   (void *)burst_buffer, 32, NULL);
  //               // if(burst_size==0) {
  //               //     break;
  //               // }
  //               // total_size = burst_size;
  //               count_break+=burst_size;
  //           }
		// 	while(i != burst_size){
  //                   diff_tsc = rte_rdtsc() - burst_buffer[i]->udata64;
  //                   if (diff_tsc < delayed_time){
  //                       // flag=1;
  //                       // count_break++;
  //                       break;
  //                       // continue;
  //                   }
  //                   do {
  //                       status = rte_ring_mp_enqueue(workers_to_tx, burst_buffer[i]);
  //                   } while (status == -ENOBUFS);
  //                   i++;
  //                   count_to_next++;
  //           }
  //           if(i==burst_size){
  //               finished=1;
  //               i=0;
  //           }else{
  //               finished=0;
  //           }
  //           break;
		// }
	}
    printf("port=%u queueid=%u  count_rx_num_nic =%u\n",portid,queueid,count_rx_num_nic );
    printf("count_break = %u\n", count_break);
    printf("count_to_next **= %u\n", count_to_next);
}


static void
worker_thread(unsigned portid)
{
	uint16_t burst_size = 0;
	struct rte_mbuf *burst_buffer[PKT_BURST_WORKER];
	uint64_t diff_tsc;
	uint64_t delay_dif_k =1;
	uint16_t i;
	unsigned lcore_id;
	int status;
	unsigned count=0;
	lcore_id = rte_lcore_id();
	RTE_LOG(INFO, DEMU, "Entering main worker on lcore %u, portId:%u\n", lcore_id,portid);
	unsigned count_in_ring = 0;
	unsigned count_i=0;
	void ** temp_ring_point;
	unsigned ring_empty_count=0;
	while (!force_quit) {
     //    if(rte_ring_count(header_pointers)>0){
     //    	// RTE_LOG(INFO, DEMU, "worker if\n");
     //        void ** temp_ring_point;
     //        int headpointers=rte_ring_mc_dequeue(header_pointers,
     //                    &(temp_ring_point));
     //        if(headpointers ==0){
     //            // RTE_LOG(INFO,DEMU,"get from headpo ss ,headpoint left = %u",rte_ring_count(header_pointers));
     //            struct rte_ring * one = *temp_ring_point;
     //            burst_size = rte_ring_mc_dequeue_burst(one,(void *)burst_buffer, PKT_BURST_WORKER, NULL);
     //            if (unlikely(burst_size == 0)){
     //            	// printf("worker ring empty %u\n",portid);//--------------------------------------------
					// continue;
     //            }
     //        }
           
     //    }

        int headpointers=rte_ring_mc_dequeue(header_pointers,
                    &(temp_ring_point));
        if(headpointers ==0){
        // if(temp_ring_point!=NULL){
        	// if(headpointers !=0){printf("error ----------\n");}
            // RTE_LOG(INFO,DEMU,"get from headpo ss ,headpoint left = %u",rte_ring_count(header_pointers));
            struct rte_ring * one = *temp_ring_point;
            burst_size = rte_ring_mc_dequeue_burst(one,(void *)burst_buffer, PKT_BURST_WORKER, NULL);
            if (unlikely(burst_size == 0)){
            	// printf("worker ring empty %u\n",portid);//--------------------------------------------
            	// ring_empty_count++;
				continue;
            }
        }
		i = 0;
		while (i < burst_size) {
			/* Add a given delay when a packet comes from the port 0.
			 * FIXME: fix this implementation.
			 */
			
			rte_prefetch0(rte_pktmbuf_mtod(burst_buffer[i], void *));
			diff_tsc = rte_rdtsc() - burst_buffer[i]->udata64;
			if (diff_tsc < delayed_time )
				continue;

			if (limit_speed) {
				uint16_t pkt_size_bit = burst_buffer[i]->pkt_len * 8;

				if (amount_token >= pkt_size_bit)
					amount_token -= pkt_size_bit;
				else
					continue;
			}
			do {
				status = rte_ring_mp_enqueue(workers_to_tx, burst_buffer[i]);
			} while (status == -ENOBUFS);
			i++;
		}
		burst_size=0;
	}
	printf("ring_empty_count =%u\n",ring_empty_count );
}

static int
demu_launch_one_lcore(__attribute__((unused)) void *dummy)
{
	unsigned lcore_id;
	lcore_id = rte_lcore_id();

	// switch(lcore_id){
	// 	case 2:demu_rx_loop(1);break;
	// 	case 3:demu_tx_loop(0);break;
	// 	case 4:worker_thread(1);break;
	// 	case 5:worker_thread(2);break;
	// 	case 6:worker_thread(3);break;
	// 	case 7:worker_thread(4);break;
	// 	case 8:worker_thread(5);break;
	// 	case 9:worker_thread(6);break;
	// 	case 10:worker_thread(7);break;
	// 	case 11:worker_thread(8);break;
	// }

    switch(lcore_id){
        case 2:demu_tx_loop(0);break;
        case 3:rx_delay_thread(1,0,rx_to_workers_arr[0],&amount_token);break;
        case 4:rx_delay_thread(1,1,rx_to_workers_arr[1],&amount_token2);break;
        case 5:rx_delay_thread(1,2,rx_to_workers_arr[2],&amount_token3);break;
        case 6:rx_delay_thread(1,3,rx_to_workers_arr[3],&amount_token4);break;
        // case 7:rx_delay_thread(1,4,rx_to_workers_arr[4]);break;
        // case 8:rx_delay_thread(1,5,rx_to_workers_arr[5]);break;
        // case 9:rx_delay_thread(1,6,rx_to_workers_arr[6]);break;
        // case 10:rx_delay_thread(1,7,rx_to_workers_arr[7]);break;
        case 7:if(limit_speed){
        	RTE_LOG(INFO, DEMU, " a** Limit speed is %lu bps\n", limit_speed);
        	demu_timer_loop();
        	RTE_LOG(INFO, DEMU, " a** Limit \n");
        }
        // case 11:rx_delay_thread(1,3,rx_to_workers_arr[8]);break;
        // case 7:worker_thread(4);break;
        // case 8:worker_thread(5);break;
        // case 9:worker_thread(6);break;
        // case 10:worker_thread(7);break;
        // case 11:worker_thread(8);break;
    }

	// if (lcore_id == TX_THREAD_CORE){
	// 	// demu_tx_loop(1);
	// 	worker_thread(4);
	// }

	// else if (lcore_id == TX_THREAD_CORE2)
	// 	demu_tx_loop(0);

	// else if (lcore_id == WORKER_THREAD_CORE){
	// 	worker_thread(1);
	// }

	// else if (lcore_id == WORKER_THREAD_CORE2){
	// 	worker_thread(2);
	// }

	// else if (lcore_id == RX_THREAD_CORE){
	// 	demu_rx_loop(1);
	// }

	// else if (lcore_id == RX_THREAD_CORE2){
	// 	worker_thread(3);
	// 	// demu_rx_loop(0);
	// }
	// else if (lcore_id == 9){
	// 	worker_thread(5);
		
	// }
	// else if (lcore_id == 10){
	// 	worker_thread(6);
		
	// }
	// else if (lcore_id == 11){
	// 	worker_thread(7);
		
	// }
	// else if (lcore_id == TIMER_THREAD_CORE){
	// 	worker_thread(8);
		
	// }
	// else if (lcore_id == 13){
	// 	worker_thread(9);
		
	// }

	// else if (limit_speed && lcore_id == TIMER_THREAD_CORE)
	// 	demu_timer_loop();

	if (force_quit)
		return 0;

	return 0;
}

/* display usage */
static void
demu_usage(const char *prgname)
{
	printf("%s [EAL options] -- -d Delayed time [us] (default is 0s)\n"
		" -p PORTMASK: HEXADECIMAL bitmask of ports to configure\n"
		" -r random packet loss %% (default is 0%%)\n"
		" -g XXX\n"
		" -s bandwidth limitation [bps]\n"
		" -D duplicate packet rate\n",
		prgname);
}

static int
demu_parse_portmask(const char *portmask)
{
	char *end = NULL;
	unsigned long pm;

	/* parse hexadecimal string */
	pm = strtoul(portmask, &end, 16);
	if ((portmask[0] == '\0') || (end == NULL) || (*end != '\0'))
		return -1;

	return pm;
}

static int
demu_parse_delayed(const char *q_arg)
{
	char *end = NULL;
	int n;

	/* parse number string */
	n = strtol(q_arg, &end, 10);
	if ((q_arg[0] == '\0') || (end == NULL) || (*end != '\0'))
		return -1;

	return n;
}

static int64_t
demu_parse_speed(const char *arg)
{
	int64_t speed, base;
	char *end = NULL;

	speed = strtoul(arg, &end, 10);
	if (end != NULL) {
		char unit = *end;

		switch (unit) {
			case 'k':
			case 'K':
				base = 1000;
				break;
			case 'm':
			case 'M':
				base = 1000 * 1000;
				break;
			case 'g':
			case 'G':
				if (speed > 10) return -1;
				base = 1000 * 1000 * 1000;
				break;
			default:
				return -1;
		}
		end++;
	}

	if (arg[0] == '\0' || end == NULL || *end != '\0') {
		return -1;
	}

	speed = speed * base;
	if (speed < 1000 && 10000000000 < speed)
		return -1;

	return speed;
}

/* Parse the argument given in the command line of the application */
static int
demu_parse_args(int argc, char **argv)
{
	int opt, ret;
	char **argvopt;
	char *prgname = argv[0];
	const struct option longopts[] = {
		{0, 0, 0, 0}
	};
	int longindex = 0;
	int64_t val;

	argvopt = argv;

	while ((opt = getopt_long(argc, argvopt, "d:q:g:p:r:s:D",
					longopts, &longindex)) != EOF) {

		switch (opt) {
			/* portmask */
			case 'p':
				demu_enabled_port_mask = demu_parse_portmask(optarg);
				if (demu_enabled_port_mask <= 0) {
					printf("Invalid value: portmask\n");
					demu_usage(prgname);
					return -1;
				}
				break;

			/* delayed packet */
			case 'd':
				val = demu_parse_delayed(optarg);
				if (val < 0) {
					printf("Invalid value: delayed time\n");
					demu_usage(prgname);
					return -1;
				}
				delayed_time = (rte_get_tsc_hz() + US_PER_S - 1) / US_PER_S * val;
				break;
			// 分流队列数量
			case 'q':
			val = demu_parse_delayed(optarg);
			if (val < 0) {
				printf("Invalid value: queue_num\n");
				demu_usage(prgname);
				return -1;
			}
			// printf("case q%d\n",val );
			queue_num =  val;
			break;

			/* random packet loss */
			case 'r':
				val = loss_random(optarg);
				if (val < 0) {
					printf("Invalid value: loss rate\n");
					demu_usage(prgname);
					return -1;
				}
				loss_percent_1 = val;
				loss_mode = LOSS_MODE_RANDOM;
				break;

			case 'g':
				val = loss_random(optarg);
				if (val < 0) {
					printf("Invalid value: loss rate\n");
					demu_usage(prgname);
					return -1;
				}
				loss_percent_2 = val;
				loss_mode = LOSS_MODE_GE;
				break;

			/* duplicate packet */
			case 'D':
				val = loss_random(optarg);
				if (val < 0) {
					printf("Invalid value: loss rate\n");
					demu_usage(prgname);
					return -1;
				}
				dup_rate = val;
				break;

			/* bandwidth limitation */
			case 's':
				val = demu_parse_speed(optarg);
				if (val < 0) {
					RTE_LOG(ERR, DEMU, "Invalid value: speed\n");
					return -1;
				}
				limit_speed = val;
				break;

			/* long options */
			case 0:
				demu_usage(prgname);
				return -1;

			default:
				demu_usage(prgname);
				return -1;
		}
	}

	if (optind >= 0)
		argv[optind-1] = prgname;

	ret = optind-1;
	optind = 0; /* reset getopt lib */
	return ret;
}

static void
check_all_ports_link_status(uint8_t port_num, uint32_t port_mask)
{
#define CHECK_INTERVAL 100 /* 100ms */
#define MAX_CHECK_TIME 90 /* 9s (90 * 100ms) in total */
	uint8_t portid, count, all_ports_up, print_flag = 0;
	struct rte_eth_link link;

	RTE_LOG(INFO, DEMU, "Checking link status\n");
	for (count = 0; count <= MAX_CHECK_TIME; count++) {
		if (force_quit)
			return;
		all_ports_up = 1;
		// RTE_LOG(INFO, DEMU, "a\n");
		for (portid = 0; portid < port_num; portid++) {
			if (force_quit)
				return;
			if ((port_mask & (1 << portid)) == 0)
				continue;
			// RTE_LOG(INFO, DEMU, "b\n");
			memset(&link, 0, sizeof(link));
			// RTE_LOG(INFO, DEMU, "c\n");
			rte_eth_link_get_nowait(portid, &link);
			/* print link status if flag set */
			if (print_flag == 1) {
				if (link.link_status)
					RTE_LOG(INFO, DEMU, "  Port %d Link Up - speed %u "
						"Mbps - %s\n", (uint8_t)portid,
						(unsigned)link.link_speed,
						(link.link_duplex == ETH_LINK_FULL_DUPLEX) ?
						("full-duplex") : ("half-duplex\n"));
				else
					RTE_LOG(INFO, DEMU, "  Port %d Link Down\n",
						(uint8_t)portid);
				continue;
			}
			/* clear all_ports_up flag if any link down */
			if (link.link_status == ETH_LINK_DOWN) {
				all_ports_up = 0;
				break;
			}
		}
		/* after finally printing all link status, get out */
		if (print_flag == 1)
			break;
		// RTE_LOG(INFO, DEMU, "d\n");
		if (all_ports_up == 0)
			rte_delay_ms(CHECK_INTERVAL);

		/* set the print_flag if all ports up or timeout */
		if (all_ports_up == 1 || count == (MAX_CHECK_TIME - 1))
			print_flag = 1;
	}
}

static void
signal_handler(int signum)
{
	if (signum == SIGINT || signum == SIGTERM) {
		RTE_LOG(NOTICE, DEMU, "Signal %d received, preparing to exit...\n",
				signum);
		force_quit = true;
	}
}

int
main(int argc, char **argv)
{
	int ret;
	uint8_t nb_ports;
	uint8_t portid;
	unsigned lcore_id;

	// ret = demu_parse_args(argc, argv);
	//RTE_LOG(INFO,DEMU,"%d, ,%d, ,%d",ENOMEM,EINVAL,EIO);
    // RTE_LOG(INFO, DEMU,"k:%lu",(rte_get_tsc_hz() + US_PER_S - 1) / US_PER_S );
	//RTE_LOG(INFO, DEMU,"k:%lu",delayed_time);
	//RTE_LOG(INFO, DEMU,"k:%PRlu",delayed_time);
	//RTE_LOG(INFO, DEMU,"k:%PRlu64",delayed_time);
	/* init EAL */
	ret = rte_eal_init(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid EAL arguments\n");
	argc -= ret;
	argv += ret;

	force_quit = false;
	signal(SIGINT, signal_handler);
	signal(SIGTERM, signal_handler);

	/* parse application arguments (after the EAL ones) */
	ret = demu_parse_args(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid DEMU arguments\n");

	/* create the mbuf pool */
	/*demu_pktmbuf_pool = rte_pktmbuf_pool_create("mbuf_pool",
			RTE_MAX(DEMU_DELAYED_BUFFER_PKTS * 2 + DEMU_SEND_BUFFER_SIZE_PKTS * 2,8192U),
			MEMPOOL_CACHE_SIZE, 0, MEMPOOL_BUF_SIZE,
			rte_socket_id()); */

	// 修改
	int headpointers_size =queue_num *4;
	// demu_pktmbuf_pool = rte_pktmbuf_pool_create("mbuf_pool",
	// 		RTE_MAX(DEMU_DELAYED_BUFFER_PKTS * queue_num + DEMU_SEND_BUFFER_SIZE_PKTS +headpointers_size+1024,8192U),
	// 		MEMPOOL_CACHE_SIZE, 0, RTE_MBUF_DEFAULT_BUF_SIZE,
	// 		rte_socket_id());
    demu_pktmbuf_pool = rte_pktmbuf_pool_create("mbuf_pool",
            DEMU_DELAYED_BUFFER_PKTS * queue_num + DEMU_SEND_BUFFER_SIZE_PKTS +headpointers_size+128*10,
            MEMPOOL_CACHE_SIZE, 0, RTE_MBUF_DEFAULT_BUF_SIZE,
            rte_socket_id());
	RTE_LOG(INFO, DEMU,"aa***a,%d,%d,%d",RTE_MBUF_DEFAULT_BUF_SIZE,MEMPOOL_BUF_SIZE,MEMPOOL_CACHE_SIZE);

	if (demu_pktmbuf_pool == NULL)
		rte_exit(EXIT_FAILURE, "Cannot init mbuf pool\n");

	nb_ports = rte_eth_dev_count();
	printf("rte_eth_dev_count= %u \n",rte_eth_dev_count() );

	if (nb_ports == 0)
		rte_exit(EXIT_FAILURE, "No Ethernet ports - bye\n");

	if (nb_ports > RTE_MAX_ETHPORTS)
		nb_ports = RTE_MAX_ETHPORTS;

	/* Initialise each port */
    //初始化0号 网卡
    // portid=0；
    // RTE_LOG(INFO, DEMU, "Initializing port %u\n", (unsigned) portid);
    // ret = rte_eth_dev_configure(portid, 1, 1, &port_conf);
    // if (ret < 0)
    //         rte_exit(EXIT_FAILURE, "Cannot configure device: err=%d, port=%u\n",
    //                 ret, (unsigned) portid);
    // rte_eth_macaddr_get(portid,&demu_ports_eth_addr[portid]);

	for (portid = 0; portid < nb_ports; portid++) {
		/* init port */
		if(portid==1){
			RTE_LOG(INFO, DEMU, "Initializing port %u\n", (unsigned) portid);
    		ret = rte_eth_dev_configure(portid, queue_num, 1, &port_conf);
    		if (ret < 0)
    			rte_exit(EXIT_FAILURE, "Cannot configure device: err=%d, port=%u\n",
    					ret, (unsigned) portid);
       
    		rte_eth_macaddr_get(portid,&demu_ports_eth_addr[portid]);

    		static struct rte_eth_conf port_conf = {
    			.rxmode = { // RX feature 见 flow_filtering
    			.split_hdr_size = 0,
    			.ignore_offload_bitfield = 1,
    			.offloads = DEV_RX_OFFLOAD_CRC_STRIP,
    			
    			},
    			.txmode = { // TX feature
    			.mq_mode = ETH_MQ_TX_NONE, //mq_多队列选项，有一些宏来定义用多队列发包的方法
    			},
    		};
    		struct rte_eth_conf local_port_conf = port_conf;
    		struct rte_eth_rxconf rxq_conf;
    		struct rte_eth_dev_info dev_info;
    		rxq_conf = dev_info.default_rxconf;
    		
    		rxq_conf.offloads = local_port_conf.rxmode.offloads;
    		
            
            ret = rte_eth_tx_queue_setup(portid, 0, 1024,
                rte_eth_dev_socket_id(portid),
                &tx_conf);
            RTE_LOG(INFO, DEMU, "test b\n");
            if (ret < 0)
                rte_exit(EXIT_FAILURE, "rte_eth_tx_queue_setup:err=%d, port=%u\n",
                        ret, (unsigned) portid);
                        		
            for (int i = 0; i < queue_num; i++) { // 设置 rx queues
                ret = rte_eth_rx_queue_setup(portid, i, nb_rxd,
                             rte_eth_dev_socket_id(portid),
                             &rxq_conf, // rx queue的配置数据，类型是 const struct rte_eth_rxconf * 指针
                             demu_pktmbuf_pool);
                if (ret < 0) {
                    rte_exit(EXIT_FAILURE,
                        ":: Rx queue setup failed: err=%d, port=%u\n",
                        ret, portid);
                }
            }
    		ret = rte_eth_dev_start(portid);
    		if (ret < 0)
    			rte_exit(EXIT_FAILURE, "rte_eth_dev_start:err=%d, port=%u\n",
    					ret, (unsigned) portid);

    		rte_eth_promiscuous_enable(portid);
    		RTE_LOG(INFO, DEMU, "  Port %u, MAC address: %02X:%02X:%02X:%02X:%02X:%02X\n",
    			(unsigned) portid,
    			demu_ports_eth_addr[portid].addr_bytes[0],
    			demu_ports_eth_addr[portid].addr_bytes[1],
    			demu_ports_eth_addr[portid].addr_bytes[2],
    			demu_ports_eth_addr[portid].addr_bytes[3],
    			demu_ports_eth_addr[portid].addr_bytes[4],
    			demu_ports_eth_addr[portid].addr_bytes[5]);
    		/* initialize port stats */
    		memset(&port_statistics, 0, sizeof(port_statistics));
		}else{ // port id=0
            RTE_LOG(INFO, DEMU, "Initializing port %u\n", (unsigned) portid);
            ret = rte_eth_dev_configure(portid, 1, 1, &port_conf);
            if (ret < 0)
                rte_exit(EXIT_FAILURE, "Cannot configure device: err=%d, port=%u\n",
                        ret, (unsigned) portid);
       
            rte_eth_macaddr_get(portid,&demu_ports_eth_addr[portid]);

                    /* init one RX queue */
                    //add 3 lines,change rx_conf  to  rxq_conf
            static struct rte_eth_conf port_conf = {
                .rxmode = { // RX feature 见 flow_filtering
                .split_hdr_size = 0,
                .ignore_offload_bitfield = 1,
                .offloads = DEV_RX_OFFLOAD_CRC_STRIP,
                
                },
                .txmode = { // TX feature
                .mq_mode = ETH_MQ_TX_NONE, //mq_多队列选项，有一些宏来定义用多队列发包的方法
                },
            };
            struct rte_eth_conf local_port_conf = port_conf;
            struct rte_eth_rxconf rxq_conf;
            struct rte_eth_dev_info dev_info;
            rxq_conf = dev_info.default_rxconf;
            
            rxq_conf.offloads = local_port_conf.rxmode.offloads;
            ret = rte_eth_tx_queue_setup(portid, 0, 1024,
                    rte_eth_dev_socket_id(portid),
                    &tx_conf);
            if (ret < 0)
                    rte_exit(EXIT_FAILURE, "rte_eth_tx_queue_setup:err=%d, port=%u\n",
                            ret, (unsigned) portid);

            ret = rte_eth_rx_queue_setup(portid, 0, nb_rxd,
                    rte_eth_dev_socket_id(portid),
                    &rxq_conf,
                    demu_pktmbuf_pool);
            if (ret < 0)
                rte_exit(EXIT_FAILURE, "rte_eth_rx_queue_setup:err=%d, port=%u\n",
                        ret, (unsigned) portid);

            ret = rte_eth_dev_start(portid);
            if (ret < 0)
                rte_exit(EXIT_FAILURE, "rte_eth_dev_start:err=%d, port=%u\n",
                        ret, (unsigned) portid);

            rte_eth_promiscuous_enable(portid);
            RTE_LOG(INFO, DEMU, "test f\n");

            RTE_LOG(INFO, DEMU, "  Port %u, MAC address: %02X:%02X:%02X:%02X:%02X:%02X\n",
                (unsigned) portid,
                demu_ports_eth_addr[portid].addr_bytes[0],
                demu_ports_eth_addr[portid].addr_bytes[1],
                demu_ports_eth_addr[portid].addr_bytes[2],
                demu_ports_eth_addr[portid].addr_bytes[3],
                demu_ports_eth_addr[portid].addr_bytes[4],
                demu_ports_eth_addr[portid].addr_bytes[5]);

            /* initialize port stats */
            memset(&port_statistics, 0, sizeof(port_statistics));
        }
			
	}
	int rule_num=queue_num;
    struct rte_flow_error errors[rule_num*2];
    struct rte_flow *flows[rule_num*2];
    int queue_seq=0;
    int rule_seq=0;
    for(;rule_seq<rule_num;rule_seq++,queue_seq++){
    		flows[rule_seq] = generate_ipv4_flow(1, queue_seq, // 将目的地ip等于192.168.1.1的数据包发送到队列号0
                SRC_IP, EMPTY_MASK,
                DEST_IP1+rule_seq, FULL_MASK, &errors[rule_seq]);
		if (!flows[rule_seq]) {
	        printf("Flow can't be created %d message: %s\n",
	            errors[rule_seq].type,
	            errors[rule_seq].message ? errors[rule_seq].message : "(no stated reason)");
	        RTE_LOG(INFO, DEMU, "test 3 end\n");
	        rte_exit(EXIT_FAILURE, "error in creating flow");
	    	}
	 //    	rule_seq++；
	 //    	// 一个队列对应两个流的情况
	 //    	flows[rule_seq] = generate_ipv4_flow(1, queue_seq, // 将目的地ip等于192.168.1.1的数据包发送到队列号0
  //               SRC_IP, EMPTY_MASK,
  //               DEST_IP1+rule_seq, FULL_MASK, &errors[rule_seq]);
		// if (!flows[rule_seq]) {
	 //        printf("Flow can't be created %d message: %s\n",
	 //            errors[rule_seq].type,
	 //            errors[rule_seq].message ? errors[rule_seq].message : "(no stated reason)");
	 //        RTE_LOG(INFO, DEMU, "test 3 end\n");
	 //        rte_exit(EXIT_FAILURE, "error in creating flow");
	 //    	}
    }
    queue_seq=0;
    for(;rule_seq<rule_num*2;rule_seq++,queue_seq++){
    		flows[rule_seq] = generate_ipv4_flow(1, queue_seq, // 将目的地ip等于192.168.1.1的数据包发送到队列号0
                SRC_IP, EMPTY_MASK,
                DEST_IP1+rule_seq, FULL_MASK, &errors[rule_seq]);
		if (!flows[rule_seq]) {
	        printf("Flow can't be created %d message: %s\n",
	            errors[rule_seq].type,
	            errors[rule_seq].message ? errors[rule_seq].message : "(no stated reason)");
	        RTE_LOG(INFO, DEMU, "test 3 end\n");
	        rte_exit(EXIT_FAILURE, "error in creating flow");
	    	}
	}

	printf("queue_num =  %d",queue_num);
	char temp_queue_id[10];
	for( int i=0;i< queue_num;i++){
		// char *temp_queue_id ;
		sprintf(temp_queue_id,"%d",i);
		// itoa(i,temp_queue_id,10);
		rx_to_workers_arr[i] = rte_ring_create(temp_queue_id, DEMU_DELAYED_BUFFER_PKTS,
			rte_socket_id(),   RING_F_SP_ENQ | RING_F_SC_DEQ);
		if (rx_to_workers_arr[i] == NULL)
			rte_exit(EXIT_FAILURE, "%s\n", rte_strerror(rte_errno));
	}
	check_all_ports_link_status(nb_ports, demu_enabled_port_mask);

    header_pointers = rte_ring_create("header_pointers", headpointers_size,
            rte_socket_id(),   RING_F_SP_ENQ | RING_F_SC_DEQ);
    if (header_pointers == NULL)
        rte_exit(EXIT_FAILURE, "can not make header pointer %s\n", rte_strerror(rte_errno));

	// rx_to_workers = rte_ring_create("rx_to_workers", DEMU_DELAYED_BUFFER_PKTS,
	// 		rte_socket_id(),   RING_F_SP_ENQ | RING_F_SC_DEQ);
	// if (rx_to_workers == NULL)
	// 	rte_exit(EXIT_FAILURE, "%s\n", rte_strerror(rte_errno));

	workers_to_tx = rte_ring_create("workers_to_tx", DEMU_SEND_BUFFER_SIZE_PKTS,
			rte_socket_id(), RING_F_SP_ENQ | RING_F_SC_DEQ);
	if (workers_to_tx == NULL)
		rte_exit(EXIT_FAILURE, "%s\n", rte_strerror(rte_errno));

	// rx_to_workers2 = rte_ring_create("rx_to_workers2", DEMU_DELAYED_BUFFER_PKTS,
	// 		rte_socket_id(),   RING_F_SP_ENQ | RING_F_SC_DEQ);

	// if (rx_to_workers2 == NULL)
	// 	rte_exit(EXIT_FAILURE, "%s\n", rte_strerror(rte_errno));

	// workers_to_tx2 = rte_ring_create("workers_to_tx2", DEMU_SEND_BUFFER_SIZE_PKTS,
	// 		rte_socket_id(), RING_F_SP_ENQ | RING_F_SC_DEQ);
	// if (workers_to_tx2 == NULL)
	// 	rte_exit(EXIT_FAILURE, "%s\n", rte_strerror(rte_errno));



	ret = 0;
	/* launch per-lcore init on every lcore */
	rte_eal_mp_remote_launch(demu_launch_one_lcore, NULL, CALL_MASTER);
	RTE_LCORE_FOREACH_SLAVE(lcore_id) {
		if (rte_eal_wait_lcore(lcore_id) < 0) {
			ret = -1;
			break;
		}
	}

	for (portid = 0; portid < nb_ports; portid++) {
		struct rte_eth_stats stats;
		/* if ((demu_enabled_port_mask & (1 << portid)) == 0) */
		/* 	continue; */
		RTE_LOG(INFO, DEMU, "Closing port %d\n", portid);
		rte_eth_stats_get(portid, &stats);
		RTE_LOG(INFO, DEMU, "port %d: in pkt: %ld out pkt: %ld in missed: %ld in errors: %ld out errors: %ld\n",
			portid, stats.ipackets, stats.opackets, stats.imissed, stats.ierrors, stats.oerrors);
		rte_eth_dev_stop(portid);
		rte_eth_dev_close(portid);
	}
	
#if defined(DEBUG_RX) || defined(DEBUG_TX)
	time_t timer;
	struct tm *timeptr;
	timer = time(NULL);
	timeptr = localtime(&timer);
#endif
#ifdef DEBUG_RX
	char filename1[64] = {'\0'};
	strftime(filename1, 64, "/home/aketa/result/rxtime%m%d%H%M%S", timeptr);
	FILE *rxoutput;
	if ((rxoutput = fopen(filename1, "a+")) == NULL) {
		printf("file open error!!\n");
		exit(EXIT_FAILURE);
	}
	for (uint64_t i = 0; i < rx_cnt - 1 ; i++) {
		fprintf(rxoutput, "%lf\n", rx_stat[i]);
	}
	fclose(rxoutput);
#endif
#ifdef DEBUG_TX
	char filename2[64] = {'\0'};
	strftime(filename2, 64, "/home/aketa/result/txtime%m%d%H%M%S", timeptr);
	FILE *txoutput;
	if ((txoutput = fopen(filename2, "a+")) == NULL) {
		printf("file open error!!\n");
		exit(EXIT_FAILURE);
	}
	for (uint64_t i = 0; i < tx_cnt - 1 ; i++) {
		fprintf(txoutput, "%lf\n", tx_stat[i]);
	}
	fclose(txoutput);
#endif


	/* rte_ring_dump(stdout, rx_to_workers); */
	/* rte_ring_dump(stdout, workers_to_tx); */

	RTE_LOG(INFO, DEMU, "Bye...\n");

	return ret;
}

static int64_t
loss_random_a(double loss_rate)
{
	double percent;
	uint64_t percent_u64;

	percent = loss_rate;
	percent *= RANDOM_MAX / 100;
	percent_u64 = (uint64_t)percent;

	return percent_u64;
}

static int64_t
loss_random(const char *loss_rate)
{
	double percent;
	uint64_t percent_u64;

	if (sscanf(loss_rate, "%lf", &percent) == 0)
		return -1;
	percent *= RANDOM_MAX / 100;
	percent_u64 = (uint64_t)percent;

	return percent_u64;
}

static bool
loss_event(void)
{
	bool lost = false;

	switch (loss_mode) {
	case LOSS_MODE_NONE:
		break;

	case LOSS_MODE_RANDOM:
		if (unlikely(loss_event_random(loss_percent_1) == true))
			lost = true;
		break;

	case LOSS_MODE_GE:
		if (unlikely(loss_event_GE(loss_random_a(0), loss_random_a(100),
			loss_percent_1, loss_percent_2) == true))
			lost = true;
		break;

	case LOSS_MODE_4STATE: /* FIX IT */
		if (unlikely(loss_event_4state(loss_random_a(100), loss_random_a(0),
			loss_random_a(100), loss_random_a(0), loss_random_a(1)) == true))
			lost = true;
		break;
	}

	return lost;
}

static bool
loss_event_random(uint64_t loss_rate)
{
	bool flag = false;
	uint64_t temp;

	temp = rte_rand() % (RANDOM_MAX + 1);
	if (loss_rate >= temp)
		flag = true;

	return flag;
}

/*
 * Gilbert Elliott loss model
 * 0: S_NOR (normal state, low loss ratio)
 * 1: S_ABN (abnormal state, high loss ratio)
 */
static bool
loss_event_GE(uint64_t loss_rate_n, uint64_t loss_rate_a, uint64_t st_ch_rate_no2ab, uint64_t st_ch_rate_ab2no)
{
#define S_NOR 0
#define S_ABN 1
	static bool state = S_NOR;
	uint64_t rnd_loss, rnd_tran;
	uint64_t loss_rate, state_ch_rate;
	bool flag = false;

	if (state == S_NOR) {
		loss_rate = loss_rate_n;
		state_ch_rate = st_ch_rate_no2ab;
	} else { // S_ABN
		loss_rate = loss_rate_a;
		state_ch_rate = st_ch_rate_ab2no;
	}

	rnd_loss = rte_rand() % (RANDOM_MAX + 1);
	if (rnd_loss < loss_rate) {
		flag = true;
	}

	rnd_tran = rte_rand() % (RANDOM_MAX + 1);
	if (rnd_tran < state_ch_rate) {
		state = !state;
	}

	return flag;
}

/*
 * Four-state Markov model
 * State 1 - Packet is received successfully in gap period
 * State 2 - Packet is received within a burst period
 * State 3 - Packet is lost within a burst period
 * State 4 - Isolated packet lost within a gap period
 * p13 is the probability of state change from state1 to state3.
 * https://www.gatesair.com/documents/papers/Parikh-K130115-Network-Modeling-Revised-02-05-2015.pdf
 */
static bool
loss_event_4state( uint64_t p13, uint64_t p14, uint64_t p23, uint64_t p31, uint64_t p32)
{
	static char state = 1;
	bool flag = false;
	uint64_t rnd = rte_rand() % (RANDOM_MAX + 1);

	switch (state) {
	case 1:
		if (rnd < p13) {
			state = 3;
		} else if (rnd < p13 + p14) {
			state = 4;
		}
		break;

	case 2:
		if (rnd < p23) {
			state = 3;
		}
		break;

	case 3:
		if (rnd < p31) {
			state = 1;
		} else if (rnd < p31 + p32) {
			state = 2;
		}
		break;

	case 4:
		state = 1;
		break;
	}

	if (state == 2 || state == 4) {
		flag = true;
	}

	return flag;
}

static bool
dup_event(void)
{
	if (unlikely(loss_event_random(dup_rate) == true))
		return true;
	else
		return false;
}
