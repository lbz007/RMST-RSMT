/*
RSMT form 
Efficient Steiner Tree Construction Based on Spanning Graphs,Hai Zhou
lbz 20190918
*/
#include<cstdio>
#include<cstring>
#include<algorithm>
#include<ctime>
#include<cmath>
#define ACC 3
#define N 10100
#define NODE N<<4
#define INF 1000000000
#define mem(a) memset(a,0,sizeof(a))
using namespace std;

int T=0,node,maxe,ee,w,q,pp,qq,m,n,i,j,xx[N<<1],yy[N<<1],yx[N<<1],f[NODE],id[NODE];
int deep,dep[NODE],en[N<<3],head[N],nex[N<<3],ls[NODE],rs[NODE],P[NODE][20];
bool vis[N<<2];
long long ans;
struct point
{
	int x;int y;int b;
	void init(int xx,int yy,int bb=0)
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
struct qu
{
	int u;int v;int e;int a;
	void init(int uu,int vv,int ee,int aa)
	{
		u=uu;v=vv;e=ee;a=aa;
	}
}query[N<<3];
int trans(int x)
{
	return lower_bound(yx+1,yx+1+n,x)-yx;
}
inline int lowbit(int x)
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
bool cmp(qu a,qu b)
{
	return a.a>b.a;
}
int mabs(int a)
{
	return a>0?a:-a;
}
void adde(int u,int v)
{
	en[++ee]=v;nex[ee]=head[u];head[u]=ee;
}
void link(int u,int v)
{
	m++;e[m].u=u;e[m].v=v;
	e[m].c=mabs(xx[u]-xx[v])+mabs(yy[u]-yy[v]);
	adde(u,v);
	adde(v,u);
	//printf("addedge: %d %d %d\n",u,v,e[m].c);
}
void addquery(int u,int v,int i)
{
	if (u==v)return;
	query[++q].init(u,v,i,0);
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
void initbit()
{
	for (i=1;i<=n;i++) c[i].a=INF;
}
int find(int x)
{
	if (f[x]==0)return x;
	return find(f[x]);
}
void topinit()
{
	q=ee=m=ans=0;node=n;
	mem(f);mem(head);mem(vis);mem(P);
	mem(dep);mem(ls);mem(rs);
}
void dfs(int u,int du)
{
	if (u==0)return;
	if (du>deep) deep=du;
	dep[u]=du;
	dfs(ls[u],du+1);
	dfs(rs[u],du+1);
}
void initlca()
{
	int i,j,k,root=node;
	dfs(root,1);
	for (i=1;i<=node;i++)
        P[i][0]=f[i];
    k=(int)(log(deep)/log(2));
    for (j=1;j<=k;j++)
        for (i=1;i<=node;i++)
            P[i][j]=P[P[i][j-1]][j-1];
}
int lca(int a,int b)
{
    int i,j,k;
    if (dep[a]>dep[b]) swap(a,b);
    k=(int)(log(dep[b])/log(2));
    for (i=k;i>=0;i--)
        if (dep[b]-(1<<i)>=dep[a])
            b=P[b][i];
    if (a==b) return a;
    k=(int)(log(dep[b])/log(2));
    for (i=k;i>=0;i--)
        if (P[a][i]!=P[b][i])
        {
            a=P[a][i];
            b=P[b][i];  
        }
    return f[a];
}

int HPWL(int x1, int y1, int x2, int y2, int x3,int y3)
{
	int i,maxx=x1,minx=x1,maxy=y1,miny=y1;
	int x[10],y[10];
	x[2]=x2;y[2]=y2;x[3]=x3;y[3]=y3;
	for(i=2;i<=3;i++) maxx=max(x[i], maxx);
	for(i=2;i<=3;i++) maxy=max(y[i], maxy);
	for(i=2;i<=3;i++) minx=min(x[i], minx);
	for(i=2;i<=3;i++) miny=min(y[i], miny);
	return maxx-minx+maxy-miny;
}
void stenpoint(int x1, int y1, int x2, int y2, int x3,int y3)
{
	point np;
 	if (x1>x2)swap(x1,x2);
 	if (y1>y2)swap(y1,y2);
 	if (y3>y2)
 	{
 	 	if (x3<x1) np.init(x1,y2);
 		if (x3>=x1 && x3<=x2) np.init(x3,y2);
		if (x3>x2) np.init(x2,y2);
	}
	if (y3<=y2 && y3>=y1)
	{ 
		if (x3<x1) np.init(x1,y3);
 		if (x3>x2) np.init(x2,y3);
	}
 	if (y3<y1)
 	{ 
	 	if (x3<x1) np.init(x1,y1);
 		if (x3>=x1 && x3<=x2) np.init(x3, y1); 
		if (x3>x2) np.init(x2,y1);
 	}
 	n++;
	xx[n]=np.x;
 	yy[n]=np.y;
}

int main()
{
	scanf("%d",&n);
	for (i=1;i<=n;i++)
		scanf("%d %d",&xx[i],&yy[i]);
	int acc=ACC;
	clock_t timstart=clock();
	while (acc--)
	{
		topinit();
		for (i=1;i<=n;i++)
			p[i].init(xx[i],yy[i],i);
		initbit();
		dealedge();
		for (i=1;i<=n;i++)
			p[i].init(xx[i],-yy[i],i);
		initbit();
		dealedge2();
		for (i=1;i<=n;i++)
			p[i].init(yy[i],xx[i],i);
		initbit();
		dealedge3();
		for (i=1;i<=n;i++)
			p[i].init(yy[i],-xx[i],i);
		initbit();
		dealedge4();
		
		sort(e+1,e+1+m,cmpe);
		for (i=1;i<=m;i++)
		{
			pp=find(e[i].u);
			qq=find(e[i].v);
			if (pp!=qq)
			{
				for (j=head[e[i].u];j>0;j=nex[j])
				{
					w=en[j];
					if (pp==find(w)) addquery(w,e[i].u,i);
					else addquery(w,e[i].v,i);
				}
				for (j=head[e[i].v];j>0;j=nex[j])
				{
					w=en[j];
					if (pp==find(w)) addquery(w,e[i].u,i);
					else addquery(w,e[i].v,i);
				}
				id[++node]=i;
				f[qq]=f[pp]=node;
				ls[node]=pp;rs[node]=qq;
				ans+=e[i].c;
			}
		}
		initlca();
		for (i=1;i<=q;i++)
		{
			maxe=id[lca(query[i].u,query[i].v)];
			query[i].a=e[maxe].c+e[query[i].e].c;
			query[i].a-=HPWL(xx[e[query[i].e].u],yy[e[query[i].e].u],xx[e[query[i].e].v],yy[e[query[i].e].v],xx[query[i].u],yy[query[i].u]);
			query[i].v=maxe;
		}
		sort(query+1,query+1+q,cmp);
		for (i=1;i<=q;i++)
		{
			if (query[i].a<=0) break;
			if (vis[query[i].e]==1 || vis[query[i].v]==1) continue;
			ans-=query[i].a;
			vis[query[i].e]=vis[query[i].v]=1;
			stenpoint(xx[e[query[i].e].u],yy[e[query[i].e].u],xx[e[query[i].e].v],yy[e[query[i].e].v],xx[query[i].u],yy[query[i].u]);
		}
	}
	clock_t timend=clock();
	printf("%.10f %lld\n",(timend-timstart)/1000.0/1000.0,ans);
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


