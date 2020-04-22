#include <iostream>
#include <vector>
#include <unordered_set>
#include <set>
#include <map>
#include <queue>
#include <algorithm>
#include <fstream>

using namespace std;

ifstream f("date.in");
ofstream g("date.out");

int nr_stari, nr_tranzitii, nr_stariFin, stareInit;
unordered_set <int> stariFin;

struct nod{
    unordered_set <int> T[27]; // T[26] ->lambda tranzitie, restul sunt tranzitii obisnuite
    ~nod() {
        for(int i = 0; i < 27; ++i)
            T[i].clear();
    }

    void operator = (const nod &ob){
        for(int i = 0; i < 27; ++i)
            T[i] = ob.T[i];
    }

};

vector <nod> G;

static char get_ch(const char &s){
    return (s == '$' ? char('z' + 1) : s);
}

static char get_muc(const int &x){
    return (x == 26 ? '$' : char(x + 'a'));
}

void addMuc(const int &nod1, const int &nod2, const char &ch){
    G[nod1].T[get_ch(ch) - 'a'].emplace(nod2);
}


void citire(){
    f >> nr_stari >> nr_tranzitii;
    G.resize(nr_stari);

    for(int i = 0; i < nr_tranzitii; ++i)
    {
        int x, y;
        char c;
        f >> x >> y >> c;
        addMuc(x, y, c);
    }

    f >> stareInit;
    f >> nr_stariFin;
    for(int i = 0; i < nr_stariFin; ++i)
    {
        int x;
        f >> x;
        stariFin.emplace(x);
    }
}

void afisare(){
    g << nr_stari << " stari\n";
    g << nr_tranzitii << " tranzitii\n";
    g << "Tranzitiile: \n";
    for(int i = 0; i < nr_stari; ++i)
        for(int tranz = 0; tranz < 27; ++tranz)
            for(auto& Nod : G[i].T[tranz])
                g << i << ' ' << Nod << ' ' << get_muc(tranz) << '\n';

    g << "Stare initiala: " << stareInit << '\n';
    g << nr_stariFin << " stari finale:\n";
    for(auto& Nod : stariFin)
        g << Nod << ' ' << '\n';
}


void lNFA_NFA(){
    //Lambda-inchiderea
    bool tranzNoi = true;
    while(tranzNoi)
    {
        tranzNoi = false;
        for(int i = 0; i < nr_stari; ++i)
            for(auto& urm : G[i].T[26])
                for(auto& tranz : G[urm].T[26])
                    if(G[i].T[26].find(tranz) == G[i].T[26].end())
                    {
                        tranzNoi = true;
                        G[i].T[26].insert(tranz);
                    }
    }
    //Eliminarea lambda-tranzitiilor
    for(int i = 0; i < nr_stari; ++i)
    {
        for(auto& urm : G[i].T[26])
        {
            for(int litera = 0; litera < 26; ++litera)
                for(auto& tranz: G[urm].T[litera])
                    G[i].T[litera].emplace(tranz);

            if(stariFin.find(urm) != stariFin.end())
                stariFin.emplace(i);
        }

        G[i].T[26].clear();
    }
    //Actualizarea automatului
    nr_stariFin = stariFin.size();
    nr_tranzitii = 0;
    for(int i = 0; i < nr_stari; ++i)
        for(int j = 0; j < 26; ++j)
            nr_tranzitii += G[i].T[j].size();
}

void NFA_DFA(){
    int nr_stari_nou = 0, nr_tranzitii_nou = 0;
    map < vector<int>, int> stariNoi; //pt redenumirea starilor
    vector <nod> G_nou;
    unordered_set <int> stariFin_nou;

    stariNoi[{stareInit}] = nr_stari_nou;
    ++nr_stari_nou;
    if(stariFin.find(stareInit) != stariFin.end())
        stariFin_nou.emplace(nr_stari_nou - 1);

    queue < vector <int> > q;
    vector <int> top, temp;
    unordered_set <int> set_temp;
    q.push({stareInit});

    while(!q.empty())
    {
        top = q.front();
        q.pop();
        for(int litera = 0; litera < 27; ++litera)
        {
            temp.clear();
            set_temp.clear();
            for(auto& pozitie : top)
                for(auto& urm : G[pozitie].T[litera])
                    if(set_temp.find(urm) == set_temp.end())
                    {
                        set_temp.emplace(urm);
                        temp.push_back(urm);
                    }

            if(temp.empty()) continue;

            sort(temp.begin(), temp.end()); //qx0, qx1, ..., qxk
            if(stariNoi.find(temp) == stariNoi.end()) //daca nu am vizitat noua stare, o vizitam
            {
                stariNoi[temp] = nr_stari_nou++;
                bool ok = false;

                for(auto& pozitie : temp) //verific daca am stare finala
                    if(stariFin.find(pozitie) != stariFin.end())
                    {
                        ok = true;
                        break;
                    }
                if(ok) //daca am stare finala, o adaug
                    stariFin_nou.emplace(nr_stari_nou - 1);

                q.push(temp);
            }

            nr_tranzitii_nou++;
            int poz = stariNoi[top]; //redenumesc starile
            if(poz >= G_nou.size())
                G_nou.resize(poz + 1);
            G_nou[poz].T[litera].emplace(stariNoi[temp]);
        }
    }
    //Actualizarea automatului
    nr_stari = nr_stari_nou;
    nr_tranzitii = nr_tranzitii_nou;
    stareInit = 0;
    stariFin.clear();
    stariFin = stariFin_nou;
    stariFin_nou.clear();
    G.clear();
    G = G_nou;
    G_nou.clear();
}

vector < vector <int> >ad; //matricea de adiacenta
unordered_set <int> viz; //pt bfs
vector <int> radacina; //pt starile finale

bool bfs(int &nodcrt, int &nr_stari_nou, unordered_set <int> &stariFin)
{
    if(viz.find(nodcrt) != viz.end())
        return false;
    ++nr_stari_nou;
    bool ok = false;
    queue <int> q;
    q.push(nodcrt);
    viz.emplace(nodcrt);

    while(!q.empty())
    {
        int vf = q.front(); q.pop();
        radacina[vf] = nr_stari_nou - 1;
        if(stariFin.find(vf) != stariFin.end()) //daca intalnim o stare finala in DFA-initial, nu o pierdem
            ok = true;

        for(auto& urm : ad[vf])
        {
            if(viz.find(urm) == viz.end())
            {
                viz.emplace(urm);
                q.push(urm);
            }
        }
    }

    return ok;
}

void DFA_DFAmin()
{
    int nr_stari_nou = 0, nr_tranzitii_nou = 0;
    unordered_set <int> stariFin_nou;
    vector <nod> G_nou;

    //Retinem nodurile "fundatura"
    vector <nod> Gfnd;
    for(int i = 0; i < nr_stari; ++i)
        for(int litera = 0; litera < 27; ++litera)
            for(auto& urm : G[i].T[litera])
                Gfnd[urm].T[litera].emplace(i);

    unordered_set <int> viz1, viz2; //viz1 pt stari in care nu pot ajunge din cea initiala,
                                    //viz2 pt starile din care nu ajung in stare finala
    queue <int> q;
    //Retin starile in care nu pot ajunge din cea initiala
    q.push(stareInit);
    viz1.emplace(stareInit);
    while(!q.empty())
    {
        int vf = q.front();
        q.pop();
        for(int litera = 0; litera < 27; ++litera)
            for(auto& urm : G[vf].T[litera])
                if(viz1.find(urm) == viz1.end())
                {
                    viz1.emplace(urm);
                    q.push(urm);
                }
    }

    //Retin starile din care nu ajung in stare finala
    for(auto& fin: stariFin)
    {
        q.push(fin);
        viz2.emplace(fin);
    }

    while(!q.empty())
    {
        int vf = q.front();
        q.pop();
        for(int litera = 0; litera < 27; ++litera)
            for(auto& urm : G[vf].T[litera])
                if(viz2.find(urm) == viz2.end())
                {
                    viz2.emplace(urm);
                    q.push(urm);
                }
    }

    //Verificam daca mai avem stari in dfa-minimal
    bool nul = false;
    if(viz2.find(stareInit) == viz2.end())
        nul = true;

    int nr = 0;
    for(auto& fin : stariFin)
        if(viz1.find(fin) != viz1.end())
            ++nr;
    if(nr == 0)
        nul = true;
    if(nul)
    {
        nr_stari = nr_tranzitii = nr_stariFin = 0;
        stareInit = -1;
        G.clear();
        Gfnd.clear(); viz1.clear(); viz2.clear();
        return ;
    }
    //Eliminam starile
    vector <int> stare_noua(nr_stari, 0);
    for(int i = 0; i < nr_stari; ++i)
        if(viz1.find(i) == viz1.end() or viz2.find(i) == viz2.end())
            stare_noua[i] = -1;
    Gfnd.clear();
    viz1.clear();
    viz2.clear();
    nr_stari_nou = nr_stari;

    int corespondent = -1;
    for(int i = 0; i < nr_stari; ++i)
        if(stare_noua[i] != -1)
            stare_noua[i] = ++corespondent;
        else
            --nr_stari_nou;

    G_nou.resize(nr_stari_nou);
    for(int i = 0; i < nr_stari; ++i)
        if(stare_noua[i] != -1) //daca nu a fost eliminat
        {
            if(stariFin.find(i) != stariFin.end())
                stariFin_nou.emplace(i);
            for(int litera = 0; litera < 27; ++litera)
                for(auto& urm : G[i].T[litera])
                    if(stare_noua[urm] != -1) //daca nu a fost eliminata
                    {
                        ++nr_tranzitii_nou;
                        G_nou[stare_noua[i]].T[litera].emplace(stare_noua[urm]); //adaug noua tranzitie
                    }
        }

    nr_stari = nr_stari_nou;
    nr_tranzitii = nr_tranzitii_nou;
    stareInit = stare_noua[stareInit];
    stariFin.clear();
    stariFin = stariFin_nou;
    stariFin_nou.clear();
    nr_stariFin = stariFin.size();
    G.clear();
    G = G_nou;
    G_nou.clear();

    //Marchez perechile de noduri echivalente
    set < pair <int,int> > check;
    for(int i = 0; i < nr_stari ; ++i)
        for(int j = i + 1; j < nr_stari; ++i)
        {
            bool x = (bool)(stariFin.find(i) != stariFin.end());
            bool y = (bool)(stariFin.find(j) != stariFin.end());
            if(x && y)
                check.emplace(make_pair(i,j));
        }

    bool ok = true;
    while(ok)
    {
        ok = false;
        vector < pair <int,int> > temp;
        for(auto& p : check)
            for(int litera = 0; litera < 27; ++litera)
            {
                if(G[p.first].T[litera].empty() or G[p.second].T[litera].empty())
                    continue;
                int x = *G[p.first].T[litera].begin();
                int y = *G[p.second].T[litera].begin();
                if(x > y)
                    swap(x,y);
                if(check.find(make_pair(x,y)) == check.end())
                {
                    temp.push_back(p);
                    break;
                }
            }
        if(!temp.empty())
            ok = true;
        for(auto& i : temp)
            check.erase(i);
        temp.clear();
    }

    //Combinam nodurile nemarcate
    ad.resize(nr_stari);
    for(auto& i : check)
        {
        ad[i.first].push_back(i.second);
        ad[i.second].push_back(i.first);
        }

    radacina.resize(nr_stari);
    for(int i = 0; i < nr_stari; ++i)
        radacina[i] = i;
    for(int i = 0; i < nr_stari; ++i)
    {
        bool fin = bfs(i, nr_stari_nou, stariFin);
        if(fin)
            stariFin_nou.emplace(nr_stari_nou - 1);
    }
    //Construim noul DFA
    G_nou.resize(nr_stari_nou);
    for(int i = 0; i < nr_stari; ++i)
        for(int litera = 0; litera < 27; ++litera)
        {
            if(G[i].T[litera].empty())
                continue;
            int x = radacina[i];
            int y = radacina[*G[i].T[litera].begin()];

            if(!G_nou[x].T[litera].empty())
                continue;
            ++nr_tranzitii_nou;
            G_nou[x].T[litera].emplace(y);
        }
    nr_stari = nr_stari_nou;
    nr_tranzitii = nr_tranzitii_nou;
    stareInit = radacina[stareInit];
    stariFin.clear();
    stariFin = stariFin_nou;
    stariFin_nou.clear();
    nr_stariFin = stariFin.size();
    G.clear();
    G = G_nou;
    G_nou.clear();
    ad.clear();
    radacina.clear();
    check.clear();
    viz.clear();
}

int main()
{
    citire();
    afisare();
    g << '\n' << '\n';
    lNFA_NFA();
    afisare();
    g << '\n' << '\n';
    NFA_DFA();
    afisare();
    g << '\n' << '\n';
    //DFA_DFAmin();
    //afisare();
    return 0;
}
