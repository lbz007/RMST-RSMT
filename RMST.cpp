#include<cstdio>
#include<cstring>
#include<algorithm>
#define N 101000
#define INF 1000000000
using namespace std;

int T=0,pp,qq,m,n,i,xx[N],yy[N],yx[N],f[N];
long long ans;
struct point
{
	int x;int y;int b;
	void init(int xx,int yy,int bb)
	{
		x=xx;y=yy;b=bb;
	}
}p[N];
struct edge
{
	int u;int v;int c;
}e[N<<2];
struct node
{
	int a;int id;
	void init(int aa,int idd)
	{
		a=aa;id=idd;
	}
}c[N];

int trans(int x)
{
	return lower_bound(yx+1,yx+1+n,x)-yx;
}
int lowbit(int x)
{
	return (x&(-x));
}
int search(int pid,int flag)
{
	int seaid=-1,sea=INF;
	int x=trans(p[pid].y-p[pid].x);
	if (flag==1) x++;
	while (x<=n)
	{
		if (sea>c[x].a)
		{
			sea=c[x].a;
			seaid=c[x].id;
		}
		x+=lowbit(x);
	}
	return seaid;
}
void add(int pid)
{
	int a=p[pid].x+p[pid].y;
	int x=trans(p[pid].y-p[pid].x);
	while (x>0)
	{
		if (c[x].a>a)
		{
			c[x].a=a;
			c[x].id=pid;
		}	
		x-=lowbit(x);
	}
}
bool cmpx(point a,point b)
{
	if (a.x!=b.x)	return a.x>b.x;
	else return a.y>b.y;
}
bool cmpx2(point a,point b)
{
	if (a.x!=b.x)	return a.x>b.x;
	else return a.y<b.y;
}
bool cmpe(edge a,edge b)
{
	return a.c<b.c;
}	
int mabs(int a)
{
	return a>0?a:-a;
}
void link(int u,int v)
{
	m++;e[m].u=u;e[m].v=v;
	e[m].c=mabs(xx[u]-xx[v])+mabs(yy[u]-yy[v]);
	//printf("addedge: %d %d %d\n",u,v,e[m].c);
}
void dealedge()
{
	int i,id;
	for (i=1;i<=n;i++)
		yx[i]=p[i].y-p[i].x;
	sort(yx+1,yx+1+n);
	sort(p+1,p+1+n,cmpx);
	add(1);
	for (i=2;i<=n;i++)
	{
		id=search(i,0);
		if (id>0)
			link(p[i].b,p[id].b);
		add(i);
	}
}
void dealedge2()
{
	int i,id;
	for (i=1;i<=n;i++)
		yx[i]=p[i].y-p[i].x;
	sort(yx+1,yx+1+n);
	sort(p+1,p+1+n,cmpx2);
	add(1);
	for (i=2;i<=n;i++)
	{
		id=search(i,0);
		if (id>0)
			link(p[i].b,p[id].b);
		add(i);
	}
}
void dealedge3()
{
	int i,id;
	for (i=1;i<=n;i++)
		yx[i]=p[i].y-p[i].x;
	sort(yx+1,yx+1+n);
	sort(p+1,p+1+n,cmpx);
	add(1);
	for (i=2;i<=n;i++)
	{
		id=search(i,1);
		if (id>0)
			link(p[i].b,p[id].b);
		add(i);
	}
}
void dealedge4()
{
	int i,id;
	for (i=1;i<=n;i++)
		yx[i]=p[i].y-p[i].x;
	sort(yx+1,yx+1+n);
	sort(p+1,p+1+n,cmpx2);
	add(1);
	for (i=2;i<=n;i++)
	{
		id=search(i,1);
		if (id>0)
			link(p[i].b,p[id].b);
		add(i);
	}
}
void init()
{
	for (i=1;i<=n;i++)
		c[i].a=INF;
}
int find(int x)
{
	if (f[x]==0)return x;
	f[x]=find(f[x]);
	return f[x];
}
int main()
{
	//freopen("123.txt","r",stdin);
	scanf("%d",&n);
	while (n>0)
	{
		T++;
		m=ans=0;
		for (i=1;i<=n;i++)
			scanf("%d %d",&xx[i],&yy[i]);
		for (i=1;i<=n;i++)
			p[i].init(xx[i],yy[i],i);
		init();
		dealedge();
		for (i=1;i<=n;i++)
			p[i].init(xx[i],-yy[i],i);
		init();
		dealedge2();
		for (i=1;i<=n;i++)
			p[i].init(yy[i],xx[i],i);
		init();
		dealedge3();
		for (i=1;i<=n;i++)
			p[i].init(yy[i],-xx[i],i);
		init();
		dealedge4();
		memset(f,0,sizeof(f));
		sort(e+1,e+1+m,cmpe);
		for (i=1;i<=m;i++)
		{
			pp=find(e[i].u);
			qq=find(e[i].v);
			if (pp!=qq)
			{
				f[pp]=qq;
				ans+=e[i].c;
			}
		}
		printf("Case %d: Total Weight = %lld\n",T,ans);
		scanf("%d",&n);
	}
	//fclose(stdin);
	return 0;
} 
/*
9
886 9383
6915 2777
8335 7793
492 5386
1421 6649
27 2362
59 8690
3926 7763
5736 9172
*/


