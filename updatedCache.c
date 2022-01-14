/*
*  A Flexible Cache Simulator by Blake Oakley
*
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <malloc.h>
#include <math.h>
#include <ctype.h>
int _l2_size;
unsigned long  **l2Cache;
int **l2Replace;
int **l2DirtyBits;
/*
* HELPER FUNCTIONS
*/
unsigned long createMask(int bits);
char returnDirty(int x);
char* getReplacement(int x);
char* getInclusion(int x);
void santize(char line[]);
void callCache2(char oper, unsigned long addr, int offsetSize, int indexSize2, int l2_assoc, int* phits2, int* pmisses2,
	int* preadMisses2, int* pwriteMisses2, int *preads2, int* pwrites2, int* pwrite_backs2, int* piterations, int* psomethingsWrong2);

int main(int argc, char *argv[])
{
	int block_size = atoi(argv[1]); //BLOCKSIZE Positive integer. Block size in bytes. (Same block size for all caches in the memory hierarchy.) Power of 2.
	int l1_size = atoi(argv[2]); //L1_SIZE: Positive integer. L1 cache size in bytes.
	int l1_assoc = atoi(argv[3]); //L1_ASSOC: Positive integer. L1 set associativity (1 is direct mapped).
	int l2_size = atoi(argv[4]); //L2_SIZE: Positive integer. L2 cache size in bytes. L2_SIZE = 0 signifies that there is no L2 cache.
	int l2_assoc = atoi(argv[5]); //L2_ASSOC: Positive integer. L2 set associativity (1 is direct mapped).
	int repl_policy = atoi(argv[6]); //REPLACEMENT_POLICY: Positive integer. 0 for LRU, 1 for PLRU , 2 for Optimal.
	int incl_policy = atoi(argv[7]); //INCLUSION_PROPERTY: Positive integer. 0 for non inclusive, 1 for inclusive.
	FILE *trace_file = fopen(argv[8], "r"); // Character string. Full name of trace file including any extensions. Contains data as Operation HexAddress
	char* trace = argv[8];
	char buff[100]; // a buffer to hold a line of data from the trace file
	int iterations = 0;//Number of iteration to keep track of LRU
	int *piterations = &iterations;

	int l1_num_of_sets = 0, l2_num_of_sets = 0;

	l1_num_of_sets = (l1_size / (block_size * l1_assoc)); // gives Number of sets for L1

	if (l2_size != 0)
	{
		l2_num_of_sets = (l2_size / (block_size * l2_assoc)); // gives Number of sets for L2
	}
	/*
	*  Create and Allocate Space for three 2D Arrays: Cache, replacement data, dirty bits
	*/
	//L1 Cache
	unsigned long **l1Cache = (unsigned long **)calloc(l1_size, sizeof(unsigned long));
	for (int i = 0; i < l1_size; i++)
	{
		l1Cache[i] = (unsigned long *)calloc(l1_assoc, sizeof(unsigned long));
	}

	//L1 Address Array
	unsigned long **addresses = (unsigned long **)calloc(l1_size, sizeof(unsigned long));
	for (int i = 0; i < l1_size; i++)
	{
		addresses[i] = (unsigned long *)calloc(l1_assoc, sizeof(unsigned long));
	}

	//L1 Cache Replacement Counter for LRU
	int **l1Replace = (int **)calloc(l1_size, sizeof(int));
	for (int i = 0; i < l1_size; i++)
	{
		l1Replace[i] = (int *)calloc(l1_assoc, sizeof(int));
	}

	//L1 Dirty Bit Tracker
	int **l1DirtyBits = (int **)calloc(l1_size, sizeof(int));
	for (int i = 0; i < l1_size; i++)
	{
		l1DirtyBits[i] = (int *)calloc(l1_assoc, sizeof(int));
	}

	if (l2_size != 0)
	{
		//L2 Cache
		l2Cache = (unsigned long **)calloc(l2_size, sizeof(unsigned long));
		for (int i = 0; i < l2_size; i++)
		{
			l2Cache[i] = (unsigned long *)calloc(l2_assoc, sizeof(unsigned long));
		}

		//L2 Cache Replacement Counter for LRU
		l2Replace = (int **)calloc(l2_size, sizeof(int));
		for (int i = 0; i < l2_size; i++)
		{
			l2Replace[i] = (int *)calloc(l2_assoc, sizeof(int));
		}

		//L2 Dirty Bit Tracker
		l2DirtyBits = (int **)calloc(l2_size, sizeof(int));
		for (int i = 0; i < l2_size; i++)
		{
			l2DirtyBits[i] = (int *)calloc(l2_assoc, sizeof(int));
		}
	}

	char oper;
	unsigned long addr, set, tag, withoutOffset, mask, evicted;
	int access_hit; // Was there a hit? 1 = True, 0 = False
	int index_of_hit; // Where did the hit occur in the cache?
	int hits = 0; //How many hits
	int misses = 0, readMisses = 0, writeMisses = 0; //how many misses

	int reads = 0; // Counts number of 'r' operations
	int writes = 0; // Counts number of 'w' operations
	int write_backs = 0; // Writes to memory upon eviction (Rs and Ws)

	int hits2 = 0; //How many hits
	int misses2 = 0, readMisses2 = 0, writeMisses2 = 0; //how many misses
	int reads2 = 0; // Counts number of 'r' operations
	int writes2 = 0; // Counts number of 'w' operations
	int write_backs2 = 0; // Writes to memory upon eviction (Rs and Ws)

	int *phits2 = &hits2; //How many hits
	int *pmisses2 = &misses2, *preadMisses2 = &readMisses2, *pwriteMisses2 = &writeMisses2; //how many misses
	int *preads2 = &reads2; // Counts number of 'r' operations
	int *pwrites2 = &writes2; // Counts number of 'w' operations
	int *pwrite_backs2 = &write_backs2; // Writes to memory upon eviction (Rs and Ws)

	int offsetSize = (int)log2((double)block_size);
	int indexSize = (int)(log2((double)l1_size / (block_size * l1_assoc)));
	int indexSize2 = (int)(log2((double)l2_size / (block_size * l2_assoc)));

	int somethingsWrong = 0;
	int somethingsWrong2 = 0;
	int *psomethingsWrong2 = &somethingsWrong2;

	//PRIMARY LOOP****************************
	while (!feof(trace_file))
	{
		fgets(buff, sizeof(buff), trace_file); //Get operation (R or W) and Address
		santize(buff);
		oper = buff[0]; // Grabs the first char of the line, a 'r' or a 'w'
		addr = strtoul(&buff[2], NULL, 16); //Grabs the hexadecimal address (e.g. 42351e38)
		withoutOffset = addr >> offsetSize;
		mask = createMask(indexSize);
		set = withoutOffset & mask;
		withoutOffset >>= indexSize; // The tag
		tag = withoutOffset;

		access_hit = 0; //Initialize to False
		iterations++;

		if (oper == 'r')
		{
			reads++; //Keeping track of 'R's
		}
		else if (oper == 'w')
		{
			writes++; //Keeping track of 'w's
		}
		else
		{
			somethingsWrong++;
			continue; //We should not get here
		}
		/*
		*  Check for a HIT
		*/
		for (int i = 0; i < l1_assoc; i++)
		{
			if (tag == l1Cache[set][i])
			{
				hits++;
				access_hit = 1;
				index_of_hit = i;
				break;
			}
		}
		/*
		*  We have a HIT; now index a replc priority value in the replc data array and mark 'w' as dirty
		*/
		if (access_hit)
		{
			l1Replace[set][index_of_hit] = iterations; //Make the hit location 0
			if (oper == 'w')
			{
				l1DirtyBits[set][index_of_hit] = 1; //only stays not dirty for 'R's
			}
		}
		/*
		*  We have a MISS
		*/
		else
		{
			misses++; // tracks misses, used to compute miss ratio
			if (oper == 'r')
			{
				readMisses++;
			}
			else if (oper == 'w')
			{
				writeMisses++;
			}
			int evictABlock = 1; //Flag will determine control flow for empty vs non-Empty spot
			/*
			*  Check for an empty spot in the cache
			*/
			for (int i = 0; i < l1_assoc; i++)
			{
				if (l1Replace[set][i] == 0) //Empty spot found
				{
					if (oper == 'w') //Mark Dirty Bit for Writes Filling Empty Spots
					{
						l1DirtyBits[set][i] = 1;
					}
					l1Cache[set][i] = tag; //put the tag value into the cache
					addresses[set][i] = addr; //put the addr value into array
					l1Replace[set][i] = iterations; //most recent value has priority value 0
					evictABlock = 0; //do not evict a block

                    if (l2_size != 0)
                    {
                        callCache2('r', addr, offsetSize, indexSize2, l2_assoc, phits2, pmisses2,
                            preadMisses2, pwriteMisses2, preads2, pwrites2, pwrite_backs2, piterations, psomethingsWrong2);
                    }

					break; //don't keep looking for empty spots
				}
			}
			/*
			*  There are no empty spots; time to evict and replace a cache value
			*/
			if (evictABlock)
			{
				int minimum = l1Replace[set][0]; //initialize to the first location
				int min_location = 0;//initialize to 0
				for (int i = 1; i < l1_assoc; i++) //Find the block to be evicted
				{
					if (l1Replace[set][i] < minimum)
					{
						minimum = l1Replace[set][i]; //find lowest value (lru)
						min_location = i; //set to location where lru was found
					}
				}
				//Check for Dirty Bit Write Back on Evicted Value
				if (l1DirtyBits[set][min_location] == 1)
				{
					write_backs++; //happens for both 'R's and 'W's
					l1DirtyBits[set][min_location] = 0; //marked not dirty
					evicted = addresses[set][min_location]; //what to send to L2
					if (l2_size != 0 && incl_policy == 0)
					{
						callCache2('w', evicted, offsetSize, indexSize2, l2_assoc, phits2, pmisses2,
							preadMisses2, pwriteMisses2, preads2, pwrites2, pwrite_backs2, piterations, psomethingsWrong2);
					}
				}
				//Mark Dirty Bit for Writes Replacing old value
				if (oper == 'w')
				{
					l1DirtyBits[set][min_location] = 1; //only stays not dirty for 'R's
				}

				l1Cache[set][min_location] = tag; //Put it in the cache
				addresses[set][min_location] = addr;
				l1Replace[set][min_location] = iterations;

				if (l2_size != 0)
				{
					callCache2('r', addr, offsetSize, indexSize2, l2_assoc, phits2, pmisses2,
						preadMisses2, pwriteMisses2, preads2, pwrites2, pwrite_backs2, piterations, psomethingsWrong2);
				}
			}
		}
	}

	fclose(trace_file);

	printf("=====Simulatorconfiguration=====\n");
	printf("BLOCKSIZE:%d\nL1_SIZE:%d\nL1_ASSOC:%d\nL2_SIZE:%d\nL2_ASSOC:%d\n", block_size, l1_size, l1_assoc, l2_size, l2_assoc);
	printf("REPLACEMENTPOLICY:%s\nINCLUSION PROPERTY:%s\ntrace_file:%s\n", getReplacement(repl_policy), getInclusion(incl_policy), trace);
	printf("=====L1contents=====\n");

	for (int i = 0; i < l1_num_of_sets; i++)
	{
		printf("Set%d:\t", i);
		for (int j = 0; j < l1_assoc; j++)
		{
			printf("%x%c\t", (unsigned int)l1Cache[i][j], returnDirty(l1DirtyBits[i][j]));
		}
		printf("\n");
	}
    if(l2_size != 0)
    {
        printf("=====L2contents=====\n");
        for (int i = 0; i < l2_num_of_sets; i++)
        {
            printf("Set%d:\t", i);
            for (int j = 0; j < l2_assoc; j++)
                {
                    printf("%x%c\t", (unsigned int) l2Cache[i][j], returnDirty(l2DirtyBits[i][j]));
                }
            printf("\n");
        }
    }
    int total = misses + write_backs;
    double missRate2 = 0;
    if(l2_size != 0)
    {
        missRate2 = (double)readMisses2 / (double)(reads2);
        total = misses + misses2 - write_backs - write_backs2;

    }
	printf("=====Simulation results(raw)=====\n");
	printf("a.numberofL1reads:%d\n", reads);
	printf("b.numberofL1 read misses:%d\n", readMisses);
	printf("c.numberofL1 writes:%d\n", writes);
	printf("d.numberofL1 write misses:%d\n", writeMisses);
	printf("e.L1 missrate:%2.6f\n", ((double)misses / (double)(hits + misses)));
	printf("f.numberofL1 writebacks:%d\n", write_backs);
	printf("g.numberofL2 reads:%d\n", reads2);
	printf("h.numberofL2 read misses:%d\n", readMisses2);
	printf("i.numberofL2 writes:%d\n", writes2);
	printf("j.numberofL2 write misses:%d\n", writeMisses2);
	printf("k.L2missrate:%2.6f\n", missRate2);
	printf("l.numberofL2writebacks:%d\n", write_backs2);
	printf("m.totalmemorytraffic:%d\n", total);

	return 0;
}

unsigned long createMask(int bits)
{
	unsigned long ret = 0;

	for (int i = 0; i < bits; i++)
	{
		ret = (ret << 1) | 1;
	}

	return ret;
}

char returnDirty(int x)
{
	if (x == 1)
		return 'D';
	else
		return ' ';
}
char* getReplacement(int x)
{
	if (x == 0)
		return "LRU";
	else if (x == 1)
		return "PLRU";
	else
		return "Optimal";
}

char* getInclusion(int x)
{
	if (x == 0)
		return "non-inclusive";
	else
		return "inclusive";
}
void santize(char line[])
{
	int offset = 0;
	while (tolower(line[offset]) != 'w' && tolower(line[offset]) != 'r' && offset < strlen(line))
	{
		offset++;
	}

	if (offset != 0)
	{
		memcpy(line, &line[offset], strlen(line));
	}
}
void callCache2(char oper, unsigned long addr, int offsetSize, int indexSize2, int l2_assoc, int* phits2, int* pmisses2,
	int* preadMisses2, int* pwriteMisses2, int *preads2, int* pwrites2, int* pwrite_backs2, int* piterations, int* psomethingsWrong2)
{
	/*
	*  L2 CACHE****************
	*/
	unsigned long set, tag, withoutOffset, mask;
	int access_hit = 0; // Was there a hit? 1 = True, 0 = False
	int index_of_hit; // Where did the hit occur in the cache?

	withoutOffset = addr >> offsetSize;
	mask = createMask(indexSize2);
	set = withoutOffset & mask;
	withoutOffset >>= indexSize2; // The tag
	tag = withoutOffset;

	if (oper == 'r')
	{
		*preads2 += 1;
	}
	else if (oper == 'w')
	{
		*pwrites2 += 1;
	}
	/*
	*  Check for a HIT
	*/
	for (int i = 0; i < l2_assoc; i++)
	{
		if (tag == l2Cache[set][i])
		{
			*phits2 += 1;
			access_hit = 1;
			index_of_hit = i;
			break;
		}
	}
	/*
	*  We have a HIT; now index a replc priority value in the replc data array and mark 'w' as dirty
	*/
	if (access_hit)
	{
		l2Replace[set][index_of_hit] = *piterations; //Make the hit location 0
		if (oper == 'w')
		{
			l2DirtyBits[set][index_of_hit] = 1; //only stays not dirty for 'R's
		}
	}
	/*
	*  We have a MISS iterations
	*/
	else
	{
		*pmisses2 += 1; // tracks misses, used to compute miss ratio
		if (oper == 'r')
		{
			*preadMisses2 += 1;
		}
		else if (oper == 'w')
		{
			*pwriteMisses2 += 1;
		}
		else
        {
            *psomethingsWrong2 += 1;
        }
		int evictABlock = 1; //Flag will determine control flow for empty vs non-Empty spot
		/*
		*  Check for an empty spot in the cache
		*/
		for (int i = 0; i < l2_assoc; i++)
		{
			if (l2Replace[set][i] == 0) //Empty spot found
			{
				if (oper == 'w') //Mark Dirty Bit for Writes Filling Empty Spots
				{
					l2DirtyBits[set][i] = 1;
				}
				l2Cache[set][i] = tag; //put the addr value into the cache
				l2Replace[set][i] = *piterations; //most recent value has highest value
				evictABlock = 0; //do not evict a block
				break; //don't keep looking for empty spots
			}
		}
		/*
		*  There are no empty spots; time to evict and replace a cache value
		*/
		if (evictABlock)
		{
			int minimum = l2Replace[set][0]; //initialize to the first location
			int min_location = 0;//initialize to 0
			for (int i = 1; i < l2_assoc; i++) //Find the block to be evicted
			{
				if (l2Replace[set][i] < minimum)
				{
					minimum = l2Replace[set][i]; //find lowest value (lru)
					min_location = i; //set to location where lru was found
				}
			}
			//Check for Dirty Bit Write Back on Evicted Value
			if (l2DirtyBits[set][min_location] == 1)
			{
				*pwrite_backs2 += 1; //happens for both 'R's and 'W's
				l2DirtyBits[set][min_location] = 0; //marked not dirty
			}
			//Mark Dirty Bit for Writes Replacing old value
			if (oper == 'w')
			{
				l2DirtyBits[set][min_location] = 1; //only stays not dirty for 'R's
			}
			l2Cache[set][min_location] = tag; //Put it in the cache
			l2Replace[set][min_location] = *piterations;
		}
	}
	//END OF L2
}