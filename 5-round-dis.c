/* rijndael-alg-ref.c   v2.2   March 2002
 * Reference ANSI C code
 * authors: Paulo Barreto
 *          Vincent Rijmen
 *
 * This code is placed in the public domain.
 */


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "rijndael-alg-ref.h"
#define SC	((BC - 4) >> 1)
#include "boxes-ref.dat"

#define Round 5
#define ntest 10

word8 cipher[65536][16];
word8 cipher1[65536][16];
word8 plain[65536][16];
word8 plain1[65536][16];


static word8 shifts[3][4][2] = {
	{{0, 0},
		{1, 3},
		{2, 2},
		{3, 1}},
	
	{{0, 0},
		{1, 5},
		{2, 4},
		{3, 3}},
	
	{{0, 0},
		{1, 7},
		{3, 5},
		{4, 4}}
};

word8 mul(word8 a, word8 b) {
	/* multiply two elements of GF(2^m)
	 * needed for MixColumn and InvMixColumn
	 */
	if (a && b) return Alogtable[(Logtable[a] + Logtable[b])%255];
	else return 0;
}

void AddRoundKey(word8 a[4][MAXBC], word8 rk[4][MAXBC], word8 BC) {
	/* Exor corresponding text input and round key input bytes
	 */
	int i, j;
	
	for(i = 0; i < 4; i++)
		for(j = 0; j < BC; j++) a[i][j] ^= rk[i][j];
}

void ShiftRows(word8 a[4][MAXBC], word8 d, word8 BC) {
	/* Row 0 remains unchanged
	 * The other three rows are shifted a variable amount
	 */
	word8 tmp[MAXBC];
	int i, j;
	
	for(i = 1; i < 4; i++) {
		for(j = 0; j < BC; j++)
			tmp[j] = a[i][(j + shifts[SC][i][d]) % BC];
		for(j = 0; j < BC; j++) a[i][j] = tmp[j];
	}
}

void Substitution(word8 a[4][MAXBC], word8 box[256], word8 BC) {
	/* Replace every byte of the input by the byte at that place
	 * in the nonlinear S-box.
	 * This routine implements SubBytes and InvSubBytes
	 */
	int i, j;
	
	for(i = 0; i < 4; i++)
		for(j = 0; j < BC; j++) a[i][j] = box[a[i][j]] ;
}

void MixColumns(word8 a[4][MAXBC], word8 BC) {
	/* Mix the four bytes of every column in a linear way
	 */
	word8 b[4][MAXBC];
	int i, j;
	
	for(j = 0; j < BC; j++)
		for(i = 0; i < 4; i++)
			b[i][j] = mul(2,a[i][j])
			^ mul(3,a[(i + 1) % 4][j])
			^ a[(i + 2) % 4][j]
			^ a[(i + 3) % 4][j];
	for(i = 0; i < 4; i++)
		for(j = 0; j < BC; j++) a[i][j] = b[i][j];
}

void InvMixColumns(word8 a[4][MAXBC], word8 BC) {
	/* Mix the four bytes of every column in a linear way
	 * This is the opposite operation of Mixcolumns
	 */
	word8 b[4][MAXBC];
	int i, j;
	
	//0xe,0x9,0xd,0xb
	//0xb,0xe,0x9,0xd
	for(j = 0; j < BC; j++)
		for(i = 0; i < 4; i++)
			b[i][j] = mul(0xe,a[i][j])
			^ mul(0xb,a[(i + 1) % 4][j])
			^ mul(0xd,a[(i + 2) % 4][j])
			^ mul(0x9,a[(i + 3) % 4][j]);
	for(i = 0; i < 4; i++)
		for(j = 0; j < BC; j++) a[i][j] = b[i][j];
}

int rijndaelKeySched (word8 k[4][MAXKC], int keyBits, int blockBits, 	word8 W[MAXROUNDS+1][4][MAXBC]) {
	/* Calculate the necessary round keys
	 * The number of calculations depends on keyBits and blockBits
	 */
	int KC, BC, ROUNDS;
	int i, j, t, rconpointer = 0;
	word8 tk[4][MAXKC];
	
	switch (keyBits) {
		case 128: KC = 4; break;
		case 192: KC = 6; break;
		case 256: KC = 8; break;
		default : return (-1);
	}
	
	switch (blockBits) {
		case 128: BC = 4; break;
		case 192: BC = 6; break;
		case 256: BC = 8; break;
		default : return (-2);
	}
	
	switch (keyBits >= blockBits ? keyBits : blockBits) {
		case 128: ROUNDS = 10; break;
		case 192: ROUNDS = 12; break;
		case 256: ROUNDS = 14; break;
		default : return (-3); /* this cannot happen */
	}
	
	
	for(j = 0; j < KC; j++)
		for(i = 0; i < 4; i++)
			tk[i][j] = k[i][j];
	t = 0;
	/* copy values into round key array */
	for(j = 0; (j < KC) && (t < (ROUNDS+1)*BC); j++, t++)
		for(i = 0; i < 4; i++) W[t / BC][i][t % BC] = tk[i][j];
	
	while (t < (ROUNDS+1)*BC) {
		/* while not enough round key material calculated */
		/* calculate new values */
		for(i = 0; i < 4; i++)
			tk[i][0] ^= S[tk[(i+1)%4][KC-1]];
		tk[0][0] ^= rcon[rconpointer++];
		
		if (KC != 8)
			for(j = 1; j < KC; j++)
				for(i = 0; i < 4; i++) tk[i][j] ^= tk[i][j-1];
		else {
			for(j = 1; j < KC/2; j++)
				for(i = 0; i < 4; i++) tk[i][j] ^= tk[i][j-1];
			for(i = 0; i < 4; i++)
				tk[i][KC/2] ^= S[tk[i][KC/2 - 1]];
			for(j = KC/2 + 1; j < KC; j++)
				for(i = 0; i < 4; i++) tk[i][j] ^= tk[i][j-1];
		}
		/* copy values into round key array */
		for(j = 0; (j < KC) && (t < (ROUNDS+1)*BC); j++, t++)
			for(i = 0; i < 4; i++) W[t / BC][i][t % BC] = tk[i][j];
	}
	
	return 0;
}

/* Everything above here is code related to AES made by Barreto and Rijmen */

int randomInRange(int min, int max){
	
	int range = max - min + 1;
	int a, b, c, d;
	
	a = rand() % range;
	b = rand() % range;
	c = rand() % range;
	d = (a*b) % range;
	d = (d+c) % range;
	
	return (min + d);
	
}

word8 randomByte(){
	return (word8) randomInRange(0, 255);
}
/////////////////
void PrintXOR(const word8 block1[4][4],const word8 block2[4][4]){
	int i, j;
	for(i = 0; i < 4; i++) {
		for(j = 0; j < 4; j++) {
			printf("%02X ", block1[i][j]^block2[i][j]);
		} printf("\n");
	}
	printf("\n");
}

void Print(const word8 block1[4][4]){
	int i, j;
	for(i = 0; i < 4; i++) {
		for(j = 0; j < 4; j++)
			printf("%02X ", block1[i][j]);
		printf("\n");
	}
	printf("\n");
}


int SuperEnc5(word8 a[4][4],word8 rk[MAXROUNDS+1][4][MAXBC]){
	
	int BC = 4,r;
	
	AddRoundKey(a,rk[0],BC);
	
	for(r = 0; r < Round-1; r++) {
		Substitution(a,S,BC);
		ShiftRows(a,0,BC);
		MixColumns(a,BC);
		AddRoundKey(a,rk[r+1],BC);
	}
	Substitution(a,S,BC);
	//    ShiftRows(a,0,BC);
	//    MixColumns(a,BC);
	AddRoundKey(a,rk[Round],BC);
	
	return 0;
}

int SuperDec5(word8 a[4][4],word8 rk[MAXROUNDS+1][4][MAXBC]){
	
	int BC = 4,r;
	
	AddRoundKey(a,rk[Round],BC);
	//  InvMixColumns(a,BC);
	//  ShiftRows(a,1,BC);
	Substitution(a,Si,BC);
	
	for(r = 1; r < Round; r++) {
		AddRoundKey(a,rk[Round-r],BC);
		InvMixColumns(a,BC);
		ShiftRows(a,1,BC);
		Substitution(a,Si,BC);
	}
	
	AddRoundKey(a,rk[0],BC);
	return 0;
}
///////////////////////////////////////////////////////////////////////////////////////////////
unsigned int CheckDiagonal(word8 p[4][4]){
	int i,j,z,diagonal;
	diagonal = 0;
	for(i=0; i<4 ; i++){
		z = 0;
		for(j=0; j<4 ; j++){
			if (p[j][(i+j)%4] != 0)
				z = 1;
		}
		if (z == 0){
			diagonal^=(1<<i);
			
		}
	}
	return (diagonal);
}
///////////////////////////////////////////////////////////////////////////////////////////////
unsigned int CheckColumns(word8 p[4][4]){
	int i,j,z,column;
	column = 0;
	for(i=0; i<4 ; i++){
		z = 0;
		for(j=0; j<4 ; j++){
			if (p[j][i] != 0)
				z = 1;
		}
		if (z == 0){
			column^=(1<<i);
		}
	}
	return (column);
}
///////////////////////////////////////////////////////////////////////////////////////////////
int changingcolumn(const word8 text1[][4],const word8 text2[][4], word8 dtext[][4],word8 dtext1[][4],int column){
	int i,j,c1,c2;
	word8 tmp1[4][4];
	word8 tmp2[4][4];
	
	for(i=0; i<4 ; i++){
		for(j=0; j<4 ; j++){
			if ((column >> i)&1){
				tmp1[j][i] = text2[j][i];
				tmp2[j][i] = text1[j][i];
			}
			else{
				tmp1[j][i] = text1[j][i];
				tmp2[j][i] = text2[j][i];
			}
		}
	}
	for(i=0; i<4 ; i++){
		for(j=0; j<4 ; j++){
			dtext[j][i]=tmp1[j][i];
			dtext1[j][i]=tmp2[j][i];
		}
	}
	c2=0;
	//check equality
	c1=0;
	for(i=0; i<4 ; i++)
		for(j=0; j<4 ; j++)
			if(dtext[i][j]==text1[i][j])
				c1++;
	if(c1==16)
		c2++;
	
	c1=0;
	for(i=0; i<4 ; i++)
		for(j=0; j<4 ; j++)
			if(dtext[i][j]==text2[i][j])
				c1++;
	if(c1==16)
		c2++;
	
	if(c2!=0)
		return(1);
	
	return(0);
	
}
//////////////////////////////////////////////////////////////////////////////////////////////////
int aescase(word8 key[][8]){
	int i,j,k,diff,r,flag;
	unsigned int counter,counter1,counter2;
	int i1,i2,i3,i4;
	word8 c[4][4][4];
	word8 p[4][4][4];
	word8 rp[4][4],rp1[4][4],rp2[4][4],rp3[4][4];
	word8 temp[4][4],temp1[4][4],temp2[4][4],temp3[4][4],test[4][4],test1[4][4],test2[4][4],test3[4][4];
	word8 rk[MAXROUNDS+1][4][MAXBC];
	rijndaelKeySched(key, 128, 128, rk);
	
	for(i=0;i<4;i++)
		for(j=0;j<4;j++)
			plain[0][4*i+j] = randomByte();
	for(i=0;i<65536;i++)
		for(j=0;j<16;j++)
			plain[i][j]=plain[0][j];
	for(i=0;i<65536;i++)
		for(j=0;j<16;j++)
			plain1[i][j]=plain[0][j];

	counter=0;
	for(i1=0;i1<9;i1++){
		for(i2=0;i2<8;i2++){
			for(i3=0;i3<8;i3++){
				for(i4=0;i4<8;i4++){
					
					plain[counter][0]=randomByte();
					plain[counter][5]=randomByte();
					plain[counter][10]=randomByte();
					plain[counter][15]=randomByte();
					
					
					for(i=0; i<4 ;i++)
						for(j=0; j<4 ;j++)
							temp[i][j]=plain[counter][4*i+j];
					
					SuperEnc5(temp,rk);
					
					for(i=0; i<4 ;i++)
						for(j=0; j<4 ;j++)
							cipher[counter][4*i+j]= temp[i][j];
					counter++;
					
				}
			}
		}
	}
	counter1=0;
	counter2=0;
	for(i1=0;i1<counter;i1++){
		for(i2=i1+1;i2<counter;i2++){
			
			for(i=0; i<4 ;i++)
				for(j=0; j<4 ;j++)
					temp[i][j]=cipher[i1][4*i+j];
			
			for(i=0; i<4 ;i++)
				for(j=0; j<4 ;j++)
					temp1[i][j]=cipher[i2][4*i+j];
			
			for(r=1;r<8;r++){
				flag=0;
				flag=changingcolumn(temp,temp1,temp2,temp3,r);
				if(flag==0){
					counter2=counter2+2;
					SuperDec5(temp2,rk);
					SuperDec5(temp3,rk);
			
					for(i=0; i<4 ;i++)
						for(j=0; j<4 ;j++)
							test[i][j]=temp2[i][j] ^ temp3[i][j];
					
					if (CheckDiagonal(test)){
						
					//	printf("new\n");
					//	Print(temp2);
					//	Print(temp3);
						counter1++;
					}
				}
			}
		}
	}
	
	
	printf(" For AES, %d plaintext pair(s), p'1+p'2, in  diagonal space with |L|=3 after encrypting %d CP and derypting %d ACC\n",counter1,counter,counter2);
	
	
	return (counter1);

}
////////////////////////////////////////////////////////////////////////////////////////////////
int randompermutation(word8 key[][8]){
	int i,j,k,diff,r,flag;
	unsigned int counter,counter1,counter2;
	int i1,i2,i3,i4;
	word8 c[4][4][4];
	word8 p[4][4][4];
	word8 rp[4][4],rp1[4][4],rp2[4][4],rp3[4][4];
	word8 temp[4][4],temp1[4][4],temp2[4][4],temp3[4][4],test[4][4],test1[4][4],test2[4][4],test3[4][4];
	word8 rk[MAXROUNDS+1][4][MAXBC];
	rijndaelKeySched(key, 128, 128, rk);
	
	for(i=0;i<4;i++)
		for(j=0;j<4;j++)
			plain[0][4*i+j] = randomByte();
	for(i=0;i<65536;i++)
		for(j=0;j<16;j++)
			plain[i][j]=plain[0][j];
	for(i=0;i<65536;i++)
		for(j=0;j<16;j++)
			plain1[i][j]=plain[0][j];
	
	counter=0;
	for(i1=0;i1<9;i1++){
		for(i2=0;i2<8;i2++){
			for(i3=0;i3<8;i3++){
				for(i4=0;i4<8;i4++){
					
					plain[counter][0]=randomByte();
					plain[counter][5]=randomByte();
					plain[counter][10]=randomByte();
					plain[counter][15]=randomByte();
					
					
					for(i=0; i<4 ;i++)
						for(j=0; j<4 ;j++)
							temp[i][j]=plain[counter][4*i+j];
					
					SuperEnc5(temp,rk);
					SuperEnc5(temp,rk);
					
					for(i=0; i<4 ;i++)
						for(j=0; j<4 ;j++)
							cipher[counter][4*i+j]= temp[i][j];
					counter++;
					
				}
			}
		}
	}
	counter1=0;
	counter2=0;
	for(i1=0;i1<counter;i1++){
		for(i2=i1+1;i2<counter;i2++){
			
			for(i=0; i<4 ;i++)
				for(j=0; j<4 ;j++)
					temp[i][j]=cipher[i1][4*i+j];
			
			for(i=0; i<4 ;i++)
				for(j=0; j<4 ;j++)
					temp1[i][j]=cipher[i2][4*i+j];
			
			for(r=1;r<8;r++){
				flag=0;
				flag=changingcolumn(temp,temp1,temp2,temp3,r);
				if(flag==0){
					counter2=counter2+2;
					SuperDec5(temp2,rk);
					SuperDec5(temp3,rk);
					SuperDec5(temp2,rk);
					SuperDec5(temp3,rk);
					
					for(i=0; i<4 ;i++)
						for(j=0; j<4 ;j++)
							test[i][j]=temp2[i][j] ^ temp3[i][j];
					
					if (CheckDiagonal(test)){
						
						//	printf("new\n");
						//	Print(temp2);
						//	Print(temp3);
						counter1++;
					}
				}
			}
		}
	}
	
	
	printf("For random permutation, %d plaintext pair(s), p'1+p'2, in diagonal space with |L|=3 after encrypting %d CP and derypting %d ACC\n",counter1,counter,counter2);
	
	
	return (counter1);
	
}
////////////////////////////////////////////////////////////////////////////////////////////////
int main() {
	int BC = 4,counter=0,counter1=0,counter2=0;
	sranddev();
	word8 k[4][MAXKC];
	int i,j;
	for( i=0; i< 4; i++){
		for( j=0; j < 4; j++){
			k[i][j] = randomByte();
		}
	}
	printf("key \n");
	for( i=0; i< 4; i++){
		for( j=0; j < 4; j++){
			printf("%02X ",k[i][j]);
		}
		printf("\n");
	}
	printf("\n");
	
	for( i=0; i<ntest ; i++){
		printf("\nTest number: %d\n",i+1);
		counter+=aescase(k);
		counter1+=randompermutation(k);
	}
	printf("\n For AES, total number plaitnext pairs in diagonal space with |L|=3  are %d after %d tests \n",counter,ntest);
	printf("\n For random permutation, total number plaitnext pairs in diagonal space with |L|=3  are %d after %d tests \n",counter1,ntest);
	return (0);
}



