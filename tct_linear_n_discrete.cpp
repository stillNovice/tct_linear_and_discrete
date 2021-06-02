#include<cstdio>
#include<iostream>
#include<algorithm>
#include<functional>
#include<numeric>
#include<string.h>
#include<cstring>
#include<string>
#include<vector>
#include<complex>
#include<sstream>
#include<iterator>
#include<set>
#include<bitset>
#include<map>
#include<stack>
#include<list>
#include<queue>
#include<deque>
#include<utility>
#include "CbcModel.hpp"

// Using as solver
#include "OsiClpSolverInterface.hpp"
char type_choice;
using namespace std;
typedef vector<int> VI;
typedef long long ll;
#define fr(x, b, e) for(int x = b; x <= (e); ++x)
#define fd(x, b, e) for(int x = e; x >= (b); --x)
#define rep(x, n) for(int x = 0; x < (n); ++x)
#define VAR(v, n) __typeof(n) v = (n)
#define FILL(a, v) memset(a, v, sizeof(a))
#define sz(a) ((int)a.size())
#define FOREACH(i, c) for(VAR(i, (c).begin()); i != (c).end(); ++i)
#define pb push_back
#define st first
#define snd second
#define dbn cerr << "\n"
#define dbg(x) cerr << #x << " : " << x << " "
#define dbs(x) cerr << x << " "
#define pln(x) cout << x << "\n"
#define all(x) x.begin(),x.end()
const int INF = 100000001;
const double EPS = 10e-9;
typedef vector<VI> VVI;
typedef vector<ll> VLL;
typedef vector<double> VD;
typedef vector<string> VS;
typedef pair<int, int> PII;
typedef vector<PII> VPII;
#define pf push_front
#define mp make_pair
#define re return

const int maxn=1000;
struct node
{
    string name;
    double nr_cost;
    double cr_cost;
    int nr_dur;
    int cr_dur;
    double cost_slope;
    int max_comp;
};
struct node2
{
    string name;
    vector<pair<int,double> >opt;                 //stores the pair of duration and cost of a particular option from different discrete options
    vector<int>crashd;                            //for storing the compression of each discrete option
    int nr_dur;
};
map<string,node2>_mapD_node;                       //for mapping structure node2 with its name
map<string,vector<int> >_mapD_crashd;              //for mapping the vector "crashd" with the name of the node
map<string,vector<string> >adj;
map<string,bool>flag;
map<string,node>_map;
map<string,int>indeg;
map<string,vector<double> >__map;                   //for each vertex,stores all the constraints in which the activity appears
map<int,pair<int,int> >column;                      //maps icolumn to corresponding (duration,cost) pair
map<int,string>col_to_name;                         //maps icolumn to corresponding activity name
map<double,int> memo_dur;
vector<string>source_nodes;
vector<string>temp_nodes;
vector<string>paths[maxn];
vector<int>path_dur(maxn);
vector<double> cost_per_deadline;                   //stores the cost of all possible deadlines
vector<string>nodes_list;
vector<double>total_cost;
vector<pair<double,int> >temp_total_cost;             //stores total cost in sorted order with corresponding duration as pair
set<string>_set;
map<string,pair<int,int> >nodesTrack;
map<string,pair<int,int> >l_n_m_dur;
map<string,int>nodes_dis;
vector<string>topo_sort;
map<string,bool>visited;
map<int,vector<pair<int,double> > >schedule;                 //stores the optimal schedule for a given deadline
int deadline,t,m;
int timex,least_deadline,max_deadline;
double budget,min_budget,max_budget;
double indirect_cost;
double min_total_cost;
int  min_tot_cost_idx;
int specified_duration;
double penalty,incentive;
double total_nr_costL;                               //stores the normal project cost for linear  choice which is  also the min cost
void dfs(string s1)
{
  //cout<<s1<<endl;
    temp_nodes.pb(s1);
    if(adj[s1].empty())
    {
        for(int k=0; k<int(temp_nodes.size()); k++)
        {
            if(type_choice=='L') path_dur[t]+=_map[temp_nodes[k]].nr_dur;
            else path_dur[t]+=_mapD_node[temp_nodes[k]].nr_dur;
	    max_deadline=max(max_deadline,path_dur[t]);
            paths[t].pb(temp_nodes[k]);
        }
        t++;
    }
    for(int j=0; j<int(adj[s1].size()); j++)
    {
        dfs(adj[s1][j]);
    }
    temp_nodes.pop_back();
}
void init_map()
{
  for(int i=0;i<int(nodes_list.size());i++)
    visited[nodes_list[i]]=false;
}
void dfs2(string s1)
{
  if(visited[s1]==true) return;
  visited[s1]=true;
  timex+=1;
  nodesTrack[s1].first=timex;
  for(int j=0; j<int(adj[s1].size()); ++j)
    {
        dfs2(adj[s1][j]);
    }
  
  nodesTrack[s1].second=timex;
    topo_sort.pb(s1);
}

void inputD()
{
    while(1)
    {
        node2 fr,sec;
        int nds,dr,cst;
        cout<<"enter the name of the preceding activity :";
        cin>>fr.name;
        if(fr.name=="none") break;
        if(flag[fr.name]==0)
        {
            cout<<"enter the number of discrete choices :";
            cin>>nds;
            while(nds--)
            {
                cout<<"enter the duration :";
                cin>>dr;
                cout<<"enter corresponding cost :";
                cin>>cst;
                fr.opt.pb(mp(dr,cst));
            }
             sort(fr.opt.rbegin(),fr.opt.rend());
             fr.nr_dur=fr.opt[0].first;
	     int least_dur=fr.opt.back().first;
	     pair<int,int>p;
	     p.first=least_dur;
	     p.second=fr.nr_dur;
	     l_n_m_dur[fr.name]=p;
             for(int i=0;i<(int)fr.opt.size();i++)
             {
                 fr.crashd.pb(fr.nr_dur-fr.opt[i].first);
             }
            _mapD_crashd[fr.name]=fr.crashd;
            _mapD_node[fr.name]=fr;
            flag[fr.name]=1;
        }
	indeg[fr.name]=indeg[fr.name];
	_set.insert(fr.name);                   //for storing unique activities
        cout<<endl;
        cout<<"enter the name of the target activity :";
        cin>>sec.name;
        if(sec.name=="nil") continue;
        if(flag[sec.name]==0)
        {
            cout<<"enter the number of discrete choices :";
            cin>>nds;
            while(nds--)
            {
                cout<<"enter the duration :";
                cin>>dr;
                cout<<"enter corresponding cost :";
                cin>>cst;
                sec.opt.pb(mp(dr,cst));
            }
             sort(sec.opt.rbegin(),sec.opt.rend());
             sec.nr_dur=sec.opt[0].first;
	     int least_dur=sec.opt.back().first;
	     pair<int,int>p;
	     p.first=least_dur;
	     p.second=sec.nr_dur;
	     l_n_m_dur[sec.name]=p;
             for(int i=0;i<(int)sec.opt.size();i++)
             {
                 sec.crashd.pb(sec.nr_dur-sec.opt[i].first);
             }
            _mapD_crashd[sec.name]=sec.crashd;
            _mapD_node[sec.name]=sec;
            flag[sec.name]=1;
        }
        adj[fr.name].pb(sec.name);
        indeg[sec.name]++;
        _set.insert(sec.name);                  //for storing unique activities
        cout<<endl;
    }
}

void inputL()
{
    while(1)
    {
        node fr,sec;
        cout<<"enter the name of the preceding activity :";
        cin>>fr.name;
        if(fr.name=="none") break;
        if(flag[fr.name]==0)
        {
            cout<<"enter normal cost :";
            cin>>fr.nr_cost;
            cout<<"enter crash cost :";
            cin>>fr.cr_cost;
            cout<<"enter normal duration :";
            cin>>fr.nr_dur;
            cout<<"enter crash duration :";
            cin>>fr.cr_dur;
            fr.max_comp=(fr.nr_dur-fr.cr_dur);
	    pair<int,int> p;
	    p=mp(fr.cr_dur,fr.nr_dur);
	    l_n_m_dur[fr.name]=p;
            if(fr.max_comp==0)
	      fr.cost_slope=-100;
            else
	      fr.cost_slope=(fr.cr_cost-fr.nr_cost)/(fr.max_comp);
            _map[fr.name]=fr;
            flag[fr.name]=1;
	    total_nr_costL+=fr.nr_cost;
        }
	indeg[fr.name]=indeg[fr.name];
	_set.insert(fr.name);                   //for storing unique activities
        cout<<endl;
        cout<<"enter the name of the target activity :";
        cin>>sec.name;
        if(sec.name=="nil") continue;
        if(flag[sec.name]==0)
	  {
            cout<<"enter normal cost :";
            cin>>sec.nr_cost;
            cout<<"enter crash cost :";
            cin>>sec.cr_cost;
            cout<<"enter normal duration :";
            cin>>sec.nr_dur;
            cout<<"enter crash duration :";
            cin>>sec.cr_dur;
            sec.max_comp=(sec.nr_dur-sec.cr_dur);
	     pair<int,int> p;
	    p=mp(sec.cr_dur,sec.nr_dur);
	    l_n_m_dur[sec.name]=p;
            if(sec.max_comp==0)
	      sec.cost_slope=-100;
            else
	      sec.cost_slope=(sec.cr_cost-sec.nr_cost)/(sec.max_comp);
            _map[sec.name]=sec;
            flag[sec.name]=1;
	    total_nr_costL+=sec.nr_cost;
        }
        adj[fr.name].pb(sec.name);
        indeg[sec.name]++;
        _set.insert(sec.name);                  //for storing unique activities
        cout<<endl;
    }
}
void print_adj_list()
{
    for(map<string,vector<string> >::iterator it=adj.begin(); it!=adj.end(); ++it)
    {
      cout<<it->first<<'-';
        string s=it->first;
        for(int j=0; j<int(adj[s].size()); ++j) cout<<adj[s][j]<<' ';
	cout<<endl;
    }
}
void find_source()
{
    for(map<string,int>::iterator it2=indeg.begin(); it2!=indeg.end(); ++it2)
    {
        if(it2->second==0)
        {
            source_nodes.pb(it2->first);
        }
    }
}
void print_paths()
{
    for(int i=0; i<t; i++)
    {
        for(int j=0; j<int(paths[i].size()); j++)
            cout<<paths[i][j]<<" ";
        cout<<path_dur[i]<<endl;
    }
}
void print_nodes()
{
    rep(i,sz(nodes_list))cout<<nodes_list[i]<<' ';
}

void topological_sort()
{
  reverse(topo_sort.begin(),topo_sort.end());
}
void init_single_source()
{
  for(int i=0;i<int(nodes_list.size());++i)
    nodes_dis[nodes_list[i]]=-INF;
  for(int i=0;i<int(source_nodes.size());++i)
   nodes_dis[source_nodes[i]]=l_n_m_dur[source_nodes[i]].first;
}
void DAG_shortest_path()
{
  topological_sort();
  init_single_source();
  for(int i=0;i<int(topo_sort.size());++i)
    {
      for(int j=0;j<int(adj[topo_sort[i]].size());++j)
	{
	  if(nodes_dis[adj[topo_sort[i]][j]]<nodes_dis[topo_sort[i]]+l_n_m_dur[adj[topo_sort[i]][j]].first)
	    {
	      nodes_dis[adj[topo_sort[i]][j]]=nodes_dis[topo_sort[i]]+l_n_m_dur[adj[topo_sort[i]][j]].first;
	      least_deadline=max(least_deadline, nodes_dis[adj[topo_sort[i]][j]]);
	    }
	}
    }
}
void create_mps_file_discrete(int tmp_deadline)
{
    FILE *fp;
    fp=fopen("/home/deepak.tomar/Cbc-2.9.2/build/share/coin/Data/Sample/obj.mps","w");
    if(fp==NULL)
    {
        puts("Cannot open file");
        exit(1);
    }
    fprintf(fp,"NAME          TEST\nROWS\n N  COST\n");

    for(int i=1; i<=t; i++)
        fprintf(fp," G  CON%d\n",i);

    for(int i=0;i<int(nodes_list.size());i++)
      {
	  for(int k=0;k<2;k++)
	    fprintf(fp," E  C%d%d\n",i,k);
      }

    fprintf(fp,"COLUMNS\n");

    for(int i=0; i<int(nodes_list.size()); i++)
    {
      int len=(int)__map[nodes_list[i]].size();
      int j;
      for(j=0; j<len-1; j+=2)
        {
	  if(j==0) fprintf(fp,"    VAR%d      COST%18.1f   CON%d%18d\n",i,0.0,int(__map[nodes_list[i]][j+1]),1);
	  else     fprintf(fp,"    VAR%d      CON%d%18d   CON%d%18d\n",i,int(__map[nodes_list[i]][j]),1,int(__map[nodes_list[i]][j+1]),1);
        }
      if(len&1)
        {
	  fprintf(fp,"    VAR%d      CON%d%18d\n",i,int(__map[nodes_list[i]][j]),1);
        }
      fprintf(fp,"    VAR%d      C%d%d %18d\n",i,i,0,-1);
    }
    int col_no=nodes_list.size();
    for(int i=0;i<int(nodes_list.size());i++)
      {
	for(int j=0;j<int(_mapD_crashd[nodes_list[i]].size());j++)
	  {
	    fprintf(fp,"    X%d%d       C%d%d %18d   C%d%d %18d\n",i,j,i,0,_mapD_crashd[nodes_list[i]][j],i,1,1);
	    fprintf(fp,"    X%d%d       COST%18.1f\n",i,j,_mapD_node[nodes_list[i]].opt[j].second);
	    column[col_no]=mp(_mapD_node[nodes_list[i]].opt[j].first,_mapD_node[nodes_list[i]].opt[j].second);
	    col_to_name[col_no]=nodes_list[i];
	    col_no++;
	  } 
      }
    fprintf(fp,"RHS\n");

    for(int i=1; i<t; i+=2)
    {
        fprintf(fp,"    RHS1      CON%d%18d   CON%d%18d\n",i,path_dur[i-1]-tmp_deadline,i+1,path_dur[i]-tmp_deadline);
    }
    if(t&1)
      fprintf(fp,"    RHS1      CON%d%18d\n",t,path_dur[t-1]-tmp_deadline);

    for(int i=0;i<int(nodes_list.size());i++)
      {
	fprintf(fp,"    RHS1      C%d%d %18d   C%d%d %18d\n",i,0,0,i,1,1);
      }
    fprintf(fp,"BOUNDS\n");

    for(int i=0; i<int(nodes_list.size()); i++)
    {
      for(int j=0;j<int(_mapD_crashd[nodes_list[i]].size());j++)
	fprintf(fp," UI BND1      X%d%d %18d\n",i,j,1);
    }
    fprintf(fp,"ENDATA");

    fclose(fp);
}



void create_mps_file(int deadline)
{
    FILE *fp;
    fp=fopen("/home/deepak.tomar/Cbc-2.9.2/build/share/coin/Data/Sample/obj.mps","w");
    if(fp==NULL)
    {
        puts("Cannot open file");
        exit(1);
    }
    fprintf(fp,"NAME          TEST\nROWS\n N  COST\n");

    for(int i=1; i<=t; i++)
        fprintf(fp," G  CON%d\n",i);

    fprintf(fp,"COLUMNS\n");
    for(int i=0; i<int(nodes_list.size()); i++)
    {
        int len=(int)__map[nodes_list[i]].size();
        int j;
        for(j=0; j<len-1; j+=2)
        {
	  if(j==0) fprintf(fp,"    VAR%d      COST%18.1f   CON%d%18d\n",i,__map[nodes_list[i]][j],int(__map[nodes_list[i]][j+1]),1);
	  else     fprintf(fp,"    VAR%d      CON%d%18d   CON%d%18d\n",i,int(__map[nodes_list[i]][j]),1,int(__map[nodes_list[i]][j+1]),1);
        }
        if(len&1)
        {
	  fprintf(fp,"    VAR%d      CON%d%18d\n",i,int(__map[nodes_list[i]][j]),1);
        }
    }
    fprintf(fp,"RHS\n");

    for(int i=1; i<t; i+=2)
    {
        fprintf(fp,"    RHS1      CON%d%18d   CON%d%18d\n",i,path_dur[i-1]-deadline,i+1,path_dur[i]-deadline);
    }
    if(t&1)
      fprintf(fp,"    RHS1      CON%d%18d\n",t,path_dur[t-1]-deadline);

    fprintf(fp,"BOUNDS\n");

    for(int i=0; i<int(nodes_list.size()); i++)
    {
        fprintf(fp," UI BND1      VAR%d%18d\n",i,_map[nodes_list[i]].max_comp);
    }
    fprintf(fp,"ENDATA");

    fclose(fp);
}
/*int ub_binary_search(int low,int high,double budget,vector<double>temp_vector)
{
  while(low<=high)
    {
      int mid=(low+high)>>1;
      if(temp_vector[mid]>budget) low=mid+1;
      else high=mid-1;
    }
  return low;
  }*/
void print_schedule_for_a_deadline(int i)
{
  for(int j=0;j<int(nodes_list.size());j++)
    {
      cout<<nodes_list[j]<<"\t"<<schedule[i][j].first<<"\t"<<schedule[i][j].second<<endl;
    }
}
int b_search(int lo,int hi,double val)
{
  while(lo<hi)
    {
      int mid=(lo+hi)>>1;
      if(temp_total_cost[mid].first>val) hi=mid-1;
      else lo=mid+1;
    }
  return hi;
}
void calc_memo_dur()
{
  memo_dur[temp_total_cost[0].first]=temp_total_cost[0].second;
  for(int i=1;i<int(temp_total_cost.size());i++)
    {
      if(temp_total_cost[i].second<memo_dur[temp_total_cost[i-1].first])
	memo_dur[temp_total_cost[i].first]=temp_total_cost[i].second;
      else
	memo_dur[temp_total_cost[i].first]=memo_dur[temp_total_cost[i-1].first];
    }
}
void budget_profile()
{
 
  for(double i=min_budget;i<=max_budget;i++)
    {
      int temp=b_search(0,temp_total_cost.size()-1,i);
      // cout<<memo_dur[temp_total_cost[temp].first]<<endl;
      // cout<<"This is the schedule : "<<endl;
      // print_schedule_for_a_deadline(memo_dur[temp_total_cost[temp].first]);
      cout<<i<<"\t"<<memo_dur[temp_total_cost[temp].first]<<endl;
    }
}
void budget_problem()
{
  int idx,tmp;
  cin>>budget;
  /*for(int i=0;i<cost_per_deadline.size();i++)
    cout<<cost_per_deadline[i]<<endl;*/
  if(budget<min_budget) budget=min_budget;
  idx=b_search(0,temp_total_cost.size()-1,budget);
  tmp=memo_dur[temp_total_cost[idx].first];
  cout<<"Stated Budget : "<<budget<<endl;
  cout<<"schedule for stated budget  :- \n"<<"Duration : "<<tmp<<endl<<endl;
  for(int i=0;i<int(nodes_list.size());i++)
    {
      cout<<nodes_list[i]<<"\t"<<schedule[tmp][i].first<<"\t"<<schedule[tmp][i].second<<endl;
    }
  double tot_cost=total_cost[tmp-least_deadline];
  cout<<"Direct Cost : "<<cost_per_deadline[tmp-least_deadline]<<endl<<"Indirect Cost : "<<indirect_cost*tmp<<endl<<"Total Cost : "<<tot_cost<<endl;
}
int find_min_total_cost_idx()
{
  min_total_cost=INF;
  int idx=0;
  for(int i=0;i<int(cost_per_deadline.size());i++)
      {
	if(min_total_cost>total_cost[i])
	  {
	    min_total_cost=total_cost[i];
	    idx=i+least_deadline;
	  }
      }
  return idx;
}
void optimal_cost()
{
    cout<<"Optimal Schedule :-\n";
    cout<<"Duration : "<<min_tot_cost_idx<<endl;
      for(int i=0;i<int(nodes_list.size());i++)
	{
	  cout<<nodes_list[i]<<"\t"<<schedule[min_tot_cost_idx][i].first<<"\t"<<schedule[min_tot_cost_idx][i].second<<endl;
	}
       cout<<"Direct Cost : "<<cost_per_deadline[min_tot_cost_idx-least_deadline]<<endl<<"Indirect Cost : "<<indirect_cost*min_tot_cost_idx<<endl<<"Total Cost : "<<min_total_cost<<endl;
}
void print_schedule_for_all_deadline()
{
  for(int j=least_deadline;j<=max_deadline;j++){
    cout<<endl<<"Schedule for "<<j<<" Days :-"<<endl;
    cout<<"--------------------------------------------"<<endl;
    cout<<"Activity"<<"\t"<<"Duration"<<"\t"<<"Cost"<<endl;
    cout<<endl;
  for(int i=0;i<int(nodes_list.size());++i)
    {
      cout<<nodes_list[i]<<"\t\t"<<schedule[j][i].first<<"\t\t"<<schedule[j][i].second<<endl;
    }
  cout<<"Total Cost : "<<total_cost[j-least_deadline];
  cout<<endl;
  }
}
void print_vector(vector<double> v)
{
  for(int i=0;i<sz(v);++i) cout<<v[i]<<' ';
  cout<<endl;
}
void deadline_problem()
{
  int dead_line;
  cout<<"Enter Deadline : "<<endl;
  cin>>dead_line;
  cout<<"deadline : "<<dead_line<<endl;
  if(dead_line<=least_deadline) dead_line=least_deadline;
  double tot_cost=total_cost[dead_line-least_deadline];
  cout<<"schedule for stated deadline :-\n"<<"Duration : "<<dead_line<<endl;
  for(int i=0;i<int(nodes_list.size());i++)
    {
      cout<<nodes_list[i]<<"\t"<<schedule[dead_line][i].first<<"\t"<<schedule[dead_line][i].second<<endl;
    }
   cout<<"Direct Cost : "<<cost_per_deadline[dead_line-least_deadline]<<endl<<"Indirect Cost : "<<indirect_cost*dead_line<<endl<<"Total Cost : "<<tot_cost<<endl;
  
}
void time_cost_curve_data()
{
  for(int i=0;i<int(total_cost.size());i++)
    cout<<(i+least_deadline)<<"\t"<<total_cost[i]<<endl;
}
int main (int argc, const char *argv[])
{
    cout<<"Select the type of time/cost curve\n ";
    cout<<"Type L for Linear or D for Discrete\n\n";
    cin>>type_choice;
    //cout<<"enter project deadline:";
    //cin>>deadline;
    least_deadline=-INF;
    max_deadline=-INF;
    cout<<"Indirect Cost per day : ";
    cin>>indirect_cost;
    cout<<"Enter specified duration : "<<endl;
    cin>>specified_duration;
    cout<<"Enter Penalty : "<<endl;
    cin>>penalty;
    cout<<"Enter Incentive : "<<endl;
    cin>>incentive;
    cout<<"\nenter the precedences(type 'none' to end)\n\n";
    if(type_choice=='L') inputL();
    else inputD();

    find_source();
    // print_adj_list();
    for(int i=0; i<int(source_nodes.size()); ++i)
    {
        dfs(source_nodes[i]);
    }
    nodes_list.assign(_set.begin(),_set.end());             //storing unique vertices in a vector
//  print_nodes();
    for(int i=0; i<int(nodes_list.size()); i++) __map[nodes_list[i]].pb(_map[nodes_list[i]].cost_slope);
    for(int i=0; i<t; i++)
    {
        for(int j=0; j<int(paths[i].size()); j++)
        {
            __map[paths[i][j]].pb(i+1);
        }
    }
    init_map();
    for(int i=0; i<int(source_nodes.size()); ++i)
    {
	dfs2(source_nodes[i]);
    }
    DAG_shortest_path();
    for(int tmp_deadline=least_deadline;tmp_deadline<=max_deadline;tmp_deadline++){
//  for(int i=0;i<int(nodes_list.size());i++)
//  {
//      cout<<nodes_list[i]<<":";
//      for(int j=0;j<int(__map[nodes_list[i]].size());j++)
//      {
//          cout<<__map[nodes_list[i]][j]<<' ';
//      }
//      cout<<endl;
//  }
    if(type_choice=='L') create_mps_file(tmp_deadline);
    else create_mps_file_discrete(tmp_deadline);
    OsiClpSolverInterface solver1;
    // Read in example model
    // and assert that it is a clean model
#if defined(SAMPLEDIR)
    int numMpsReadErrors = solver1.readMps(SAMPLEDIR "/obj.mps","");
    if( numMpsReadErrors != 0 )
    {
        printf("%d errors reading MPS file\n", numMpsReadErrors);
        return numMpsReadErrors;
    }
#else
    fprintf(stderr, "Do not know where to find sample MPS files.\n");
    exit(1);
#endif

    // Pass data and solver to CbcModel
    CbcModel model(solver1);

    // uncomment to reduce printout
     model.setLogLevel(1);
    model.solver()->setHintParam(OsiDoReducePrint,true,OsiHintTry);
    // Do complete search
    model.branchAndBound();
    /* Print solution.  CbcModel clones solver so we
       need to get current copy */
    int numberColumns = model.solver()->getNumCols();
    double objective=model.solver()->getObjValue() * model.solver()->getObjSense();
    if(type_choice=='L') objective+=total_nr_costL;
    cost_per_deadline.pb(objective);
    const double * solution = model.solver()->getColSolution();
    //cout<<"deadline : "<<tmp_deadline<<endl;
    for (int iColumn=0; iColumn<numberColumns; iColumn++)
      {
	double value=solution[iColumn];
	if(type_choice=='L')
	  schedule[tmp_deadline].pb(mp(_map[nodes_list[iColumn]].nr_dur-value,_map[nodes_list[iColumn]].cost_slope*value+_map[nodes_list[iColumn]].nr_cost));
	//cout<<nodes_list[iColumn]<<"\t"<<schedule[tmp_deadline][iColumn].first<<"\t"<<schedule[tmp_deadline][iColumn].second<<endl;
	else
	  if (fabs(value)>1.0e-7&&model.solver()->isInteger(iColumn))
	    schedule[tmp_deadline].pb(column[iColumn]);
	// cout<<iColumn<< ' '<< value<<endl;
      }
    cout<<endl;
    //cout<<numberColumns<<endl;
    }
    //print_paths();
    
    for(int i=0;i<int(cost_per_deadline.size());i++)
      {
	double penalty_incurred=0,incentive_received=0;
	int diff=specified_duration-(i+least_deadline);
	if(diff>=0)
	  {
	    incentive_received=diff*incentive;
	  }
	else
	  {
	    penalty_incurred=abs(diff)*penalty;
	  }
	total_cost.pb((least_deadline+i)*indirect_cost+cost_per_deadline[i]+penalty_incurred-incentive_received);
	temp_total_cost.pb(mp(total_cost[i],i+least_deadline));
      }
    sort(all(temp_total_cost));
    min_budget=temp_total_cost[0].first;
    max_budget=temp_total_cost.back().first;
    printf("Project Normal Duration : %d\n",max_deadline);
    printf("Project Crash Duration : %d\n",least_deadline);
    cout<<"Minimum Cost : "<<min_budget<<endl;
    cout<<"Maximum Cost : "<<max_budget<<endl;
    //print_vector(cost_per_deadline);
    //print_schedule_for_all_deadline();
    cout<<"type o for Optimal Cost,b for budget,d for deadline\n";
    min_tot_cost_idx=find_min_total_cost_idx();
    calc_memo_dur();
    budget_profile();
    char choice;
    cin>>choice;
    if(choice=='o')
      optimal_cost();
    else if(choice=='b')
      budget_problem();
    else if(choice=='d')
      deadline_problem();
    //time_cost_curve_data();
    /*for(int i=nodes_list.size();i<int(nodes_list.size()+column.size());i++)
      cout<<column[i].first<<' '<<column[i].second<<endl;*/
    return 0;
}
