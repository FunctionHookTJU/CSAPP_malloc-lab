/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "TJU",
    /* First member's full name */
    "FunctionHook",
    /* First member's email address */
    "tjdx1225230685@tju.edu.cn",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* 单字（4字节）或双字（8字节）对齐，此处选择双字对齐，因此将对齐粒度定义为8字节。
   对齐操作可确保分配的内存地址是 ALIGNMENT 的整数倍，有助于提高内存访问效率。*/
#define ALIGNMENT 8

/* 向上舍入到最接近的 ALIGNMENT 的倍数 */
/* 此宏定义用于将给定的 size 值向上舍入到最接近的 ALIGNMENT（8字节）的倍数。
   具体实现原理是：先将 size 加上 ALIGNMENT - 1，然后与 ~0x7 进行按位与操作。
   ~0x7 的二进制表示为 ...11111000，按位与操作会将低3位清零，从而实现8字节对齐。*/
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

#define WSIZE 4 // 头部和脚部的大小
#define DSIZE 8 // 双字的大小

// 定义扩展堆时的默认大小
#define INITCHUNKSIZE (1 << 6)
#define CHUNKSIZE (1 << 12)
#define LISTMAX 16

/* 设置头部和脚部的值，将块大小和分配位组合在一起
 块大小（size）通常是一个整数（如 32 位或 64 位）。
分配状态（alloc）只需要一个二进制位（0 表示空闲，1 表示已分配）。*/
#define PACK(size, alloc) ((size) | (alloc))

/*读写指针p的位置*/
#define GET(p) (*(unsigned int *)(p))                // 将指针p转化为unsigned int *类型的指针，然后解引用获取该处存储的值
#define PUT(p, val) ((*(unsigned int *)(p)) = (val)) // 将指针p转化为unsigned int *类型的指针，然后将val赋值给该内存位置

/* 从头部或脚部获取大小或分配位 */
#define GET_SIZE(p) (GET(p) & ~0x7)
// 0x7是...000111反过来就是...111000，按位与操作会将低3位清零，从而获取头部的大小
#define GET_ALLOC(p) (GET(p) & 0x1)
// 0x1是...000001，按位与操作只保留最后一位，从而获取allocate位

/* 给定有效载荷指针, 找到头部和脚部 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
// 将bp转化为char *类型的指针，然后减去头部的大小，从而找到头部的位置
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
// 将bp转化为char *类型的指针，然后加上头部的大小，再减去脚部的大小，从而找到脚部的位置

#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))//设置指针p的值为ptr
/* 给定有效载荷指针, 找到前一块或下一块 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))//链表就像排队，下一块(NEXT)是你身后的人，前一块(PREV)是你面前的人，你比面前的人来的晚，面前的人来的比你早，你身后的人来的比你晚
// 将bp转化为char *类型的指针，然后加上头部的大小，再减去脚部的大小，从而找到下一块的位置
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
// 将bp转化为char *类型的指针，然后减去脚部的大小，再减去头部的大小，从而找到前一块的位置


#define PRED_PTR(ptr) ((char *)(ptr))//获取前驱指针
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)//获取后继指针

#define PRED(ptr) (*(char **)(ptr))//通过ptr获取前驱节点地址
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))//获取后继节点地址_successive

/*自定义的辅助函数*/
static void *extend_heap(size_t size);
static void insert_node(void *ptr, size_t size);
static void *coalesce(void *ptr);
static void delete_node(void *ptr);
static void *place(void *ptr, size_t size);
/*
 * mm_init - initialize the malloc package.初始化malloc包。
 */
static void *segregated_free_lists[LISTMAX]; // 分离空闲链表

int mm_init(void)
{
    int listnumber;
    char *heap; 

    /* 初始化分离空闲链表 */
    for (listnumber = 0; listnumber < LISTMAX; listnumber++)
    {
        segregated_free_lists[listnumber] = NULL;
    }

    /* 初始化堆 */
    if ((long)(heap = mem_sbrk(4 * WSIZE)) == -1)
        return -1;

    /* 这里的结构参见本文上面的“堆的起始和结束结构” */
    PUT(heap, 0);
    PUT(heap + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap + (3 * WSIZE), PACK(0, 1));

    /* 扩展堆 */
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;

    return 0;
}


/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 *     通过增加brk指针来分配一个内存块。
 *     始终分配大小为对齐粒度倍数的内存块。
 */
void *mm_malloc(size_t size){
    if (size == 0)
        return NULL;
    
    size=ALIGN(size + DSIZE);
    int listnumber = 0;
    size_t searchsize = size;
    void *ptr = NULL;
    while (listnumber < LISTMAX){
        /* 寻找对应链 */
        if (((searchsize <= 1) && (segregated_free_lists[listnumber] != NULL))){
            ptr = segregated_free_lists[listnumber];
            /* 在该链寻找大小合适的free块 */
            while ((ptr != NULL) && ((size > GET_SIZE(HDRP(ptr))))){
                ptr = PRED(ptr);//对每个链表，通过 PRED(ptr) 遍历前向指针查找合适块,找到第一个大小≥请求size的块时跳出循环
            }
            /* 找到对应的free块 */
            if (ptr != NULL)
                break;
        }
        searchsize >>= 1;//size每除以2，就给listnumber加1，用于确定链表块大小，searchsize只有1和0两种情况，根据循环需求确定。
        listnumber++;//listnumber就是searchsize除以2的次数
    }

    /* 没有找到合适的free块，扩展堆 */
    if (ptr == NULL){   
        ptr = extend_heap(MAX(size, CHUNKSIZE));
        if ( ptr == NULL )
            return NULL;
    }

    /* 在free块中allocate size大小的块 */
    ptr = place(ptr, size);

    return ptr;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr){//free不是删除内存块，而是将内存块标记为未分配，再次使用时可以直接覆盖原内容
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));//将头脚部设为未分配
    PUT(FTRP(ptr), PACK(size, 0));

    /* 将已释放的块插入分离空闲链表 */
    insert_node(ptr, size);
    /* 注意合并 */
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * 用于调整已分配内存块的大小
 */
void *mm_realloc(void *ptr, size_t size){
    void *new_block = ptr;
    int remainder;

    if (size == 0)
        return NULL;

    /* 内存对齐 */
    if (size <= DSIZE){
        size = 2 * DSIZE;
    }
    else{
        size = ALIGN(size + DSIZE);
    }

    /* 如果size小于原来块的大小，直接返回原来的块 */
    if ((remainder = GET_SIZE(HDRP(ptr)) - size) >= 0){
        return ptr;
    }
    /* 否则先检查地址连续下一个块是否为free块或者该块是堆的**结束块**，因为我们要尽可能利用相邻的free块，以此减小“external fragmentation” */
    else if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr))))/*获取下一个块的大小，堆结束块（哨兵块） ：被设计为 大小为0的特殊块 ，作为堆的边界标记*//*空闲块或者是堆的结束块*/
    {
        /* 即使加上后面连续地址上的free块空间也不够，需要扩展块 */
        remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - size;//剩余空间大小是当前块大小加上下一个块大小减去请求大小
        if (remainder < 0){/*如果大小不够请求*/
            if (extend_heap(MAX(-remainder, CHUNKSIZE)) == NULL)/*extend_heap函数的类型是void指针*/
                return NULL;
            remainder += MAX(-remainder, CHUNKSIZE);
        }

        /* 删除刚刚利用的free块并设置新块的头尾 */
        delete_node(NEXT_BLKP(ptr));
        PUT(HDRP(ptr), PACK(size + remainder, 1));
        PUT(FTRP(ptr), PACK(size + remainder, 1));
    }
    /* 没有可以利用的连续free块，而且size大于原来的块，这时只能申请新的不连续的free块、复制原块内容、释放原块 */
    else{
        new_block = mm_malloc(size);//利用memcpy复制原内存块中内容 
        /*extern void *memcpy (void *__restrict __dest, const void *__restrict __src, size_t __n) __THROW __nonnull ((1, 2));*/
        // 将 源内存块 （ __src ）的 前 __n 字节 复制到 目标内存块 （ __dest ），返回目标内存块指针
        memcpy(new_block, ptr, GET_SIZE(HDRP(ptr)));
        mm_free(ptr);
    }
    return new_block;
}

static void *extend_heap(size_t size){/*该函数用于扩展堆空间*/
    void *ptr;
    /*内存对齐，将所需要的size向上取整为8的倍数*/
    size = ALIGN(size);
    /*系统调用mem_sbrk扩展堆  mem_sbrk - sbrk函数的简单模型。
    通过incr字节扩展堆，并返回新区域的起始地址。在此模型中，堆不能收缩。*/
    ptr = mem_sbrk(size);
    if ( ptr == (void *)-1)//(void *)-1表示错误状态，扩展失败
        return NULL;
    /* 设置刚刚扩展的free块的头和尾 */
    PUT(HDRP(ptr), PACK(size, 0));//标记块alloc=0表示为空闲状态
    PUT(FTRP(ptr), PACK(size, 0));//头部和脚部存储相同信息 便于向前或向后合并空闲块

    /* 注意这个块是堆的结尾，所以还要设置一下结尾 */
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));/*`NEXT_BLKP`获取下一个块的指针  
    哨兵块设计 ：
    大小 0 ：表示这是一个特殊块
    alloc=1 ：标记为已分配
    作用：防止堆越界访问，简化边界条件判断*/
    /* 扩展块完成后将其插入到分离空闲链表中 */
    insert_node(ptr, size);
    /* 另外这个free块的前面也可能是一个free块，可能需要合并 */
    return coalesce(ptr);//合并当前块与前后相邻的空闲块，减少内存碎片
}



static void insert_node(void *ptr, size_t size)
/*该函数将一个空闲块插入到分离空闲链表中，首先根据块的大小找到对应的链表，
然后在该链表中寻找合适的插入位置，保证链表中块按大小从小到大排序，最后根据不同情况完成插入操作。*/
{
    int listnumber = 0; // 链表编号
    void *search_ptr = NULL;
    void *insert_ptr = NULL;

    /* 通过块的大小找到对应的链 */
    while ((listnumber < LISTMAX - 1) && (size > 1))
    {//通过右移操作计算块大小对应的链表编号
        size = size>> 1; /* size /= 2 */
        listnumber++;
    }

    /* 找到对应的链后，在该链中继续寻找对应的插入位置，以此保持链中块由小到大的特性 */
    search_ptr = segregated_free_lists[listnumber];
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr))))
    { //   从链表头开始遍历           比较块大小，寻找第一个大于当前块的位置 
        insert_ptr = search_ptr;
        search_ptr = PRED(search_ptr); // PRED获取链表节点的前驱指针
    }

    /*插入操作： 循环后有四种情况 */
    if (search_ptr != NULL)
    {
        /* 1. ->xx->insert->xx 在中间插入*/
        if (insert_ptr != NULL)//search和insert都不为空
        {
            SET_PTR(PRED_PTR(ptr), search_ptr);//ptr的前一个节点是search_ptr
            SET_PTR(SUCC_PTR(search_ptr), ptr);//search_ptr的后一个节点是ptr
            SET_PTR(SUCC_PTR(ptr), insert_ptr);//ptr的后一个节点是insert_ptr
            SET_PTR(PRED_PTR(insert_ptr), ptr);//insert_ptr的前一个节点是ptr
        }
        /* 2. [listnumber]->insert->xx 在开头插入，而且后面有之前的free块*/
        else//insert为空，search不为空
        {
            SET_PTR(PRED_PTR(ptr), search_ptr);//ptr的前一个节点是search_ptr
            SET_PTR(SUCC_PTR(search_ptr), ptr);//search_ptr的后一个节点是ptr
            SET_PTR(SUCC_PTR(ptr), NULL);//ptr的后一个节点为空
            segregated_free_lists[listnumber] = ptr;//链表头指向ptr
        }
    }
    else
    {
        if (insert_ptr != NULL)//search为空，insert不为空
        { /* 3. ->xxxx->insert 在结尾插入*/
            SET_PTR(PRED_PTR(ptr), NULL);//search_ptr为空
            SET_PTR(SUCC_PTR(ptr), insert_ptr);//ptr的后一个节点是insert_ptr
            SET_PTR(PRED_PTR(insert_ptr), ptr);//insert_ptr的前一个节点是ptr
        }
        else//search为空，insert为空
        { /* 4. [listnumber]->insert 该链为空，这是第一次插入 */
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[listnumber] = ptr;//insert和search都为空，ptr直接成为链表头
        }
    }
}
static void delete_node(void *ptr){/*删除节点*/
    int listnumber = 0;
    size_t size = GET_SIZE(HDRP(ptr));

    /* 通过块的大小找到对应的链 操作方式和insert_node相同*/
    while ((listnumber < LISTMAX - 1) && (size > 1)){
        size >>= 1;
        listnumber++;
    }

    /* 根据这个块的情况分四种可能性 前导指针和后继指针空或非空*/
    if (PRED(ptr) != NULL){
        /* 1. xxx-> ptr -> xxx 两者都非空，表示该块处于链表中间位置*/
        if (SUCC(ptr) != NULL){
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
        }
        /* 2. [listnumber] -> ptr -> xxx */
        /*前导指针为非空，后继指针空，表示该块是链表的尾节点，有前驱节点没有后继节点 */
        else{
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
            segregated_free_lists[listnumber] = PRED(ptr);
        }
    }
    else if(PRED(ptr) == NULL){
        /* 3. [listnumber] -> xxx -> ptr */
        if (SUCC(ptr) != NULL){
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
        }
        /* 4. [listnumber] -> ptr */
        else{
            segregated_free_lists[listnumber] = NULL;//链表只有一个节点的话就直接删除该链表
        }
    }
}

//合并空闲块的函数
static void *coalesce(void *ptr)
{
    _Bool is_prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));//查看前一个、后一个块是否已分配
    _Bool is_next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));//从头部获取当前块的大小
    /* 根据ptr所指向块前后相邻块的情况，可以分为四种可能性 */
    /* 另外注意到由于我们的合并和申请策略，不可能出现两个相邻的free块 */
    /* 1.前后均为allocated块，不做合并，直接返回 */
    if (is_prev_alloc && is_next_alloc)
    {
        return ptr;
    }
    /* 2.前面的块是allocated，但是后面的块是free的，这时将两个free块合并 */
    else if (is_prev_alloc && !is_next_alloc)
    {
        delete_node(ptr);
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));//将合并后的块信息更新到头部和脚部
        PUT(FTRP(ptr), PACK(size, 0));
    }
    /* 3.后面的块是allocated，但是前面的块是free的，这时将两个free块合并 */
    else if (!is_prev_alloc && is_next_alloc)//   |prev是free|在此处合并|ptr是free|next是allocated|
    {
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    /* 4.前后两个块都是free块，这时将三个块同时合并 */
    else
    {
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }

    /* 将合并好的free块加入到空闲链接表中 */
    insert_node(ptr, size);

    return ptr;
}

static void *place(void *ptr, size_t size){/*该函数负责将空闲块分割并分配给用户，size是要请求的内存大小*/
    size_t ptr_size = GET_SIZE(HDRP(ptr));//获取ptr当前块大小
    /* allocate size大小的空间后剩余的大小 */
    size_t remainder = ptr_size - size;
    delete_node(ptr);/*因为当一个空闲块被选中分配给用户时，必须立即从链表中删除*/

    /* 如果剩余的大小小于最小块，则不分离原块 */
    if (remainder < DSIZE * 2){
        PUT(HDRP(ptr), PACK(ptr_size, 1));//就是直接把delete_note删掉的东西原样放回去
        PUT(FTRP(ptr), PACK(ptr_size, 1));
    }
    else if (size >= 96){//特殊分割
        // 将原块前半部分设为空闲块
        PUT(HDRP(ptr), PACK(remainder, 0));
        PUT(FTRP(ptr), PACK(remainder, 0));
        // 将后半部分设为分配块
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(size, 1));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 1));
        // 将空闲部分重新插入链表
        insert_node(ptr, remainder);
        return NEXT_BLKP(ptr);
    }

    else {
        // 当请求分配的内存大小 < 96 字节时，采用常规分割策略：将原块前半部分分配给用户，后半部分保留为空闲块
        // 将当前块的前半部分标记为已分配，更新其头部和脚部信息
        PUT(HDRP(ptr), PACK(size, 1));
        PUT(FTRP(ptr), PACK(size, 1));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(remainder, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(remainder, 0));
        insert_node(NEXT_BLKP(ptr), remainder);
    }
    return ptr;
}
