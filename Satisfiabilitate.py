import time
import sys
import random  #avem nevoie pentru strategia random choice
from collections import \
    defaultdict  # importam defaultdict, un fel de dictionar mai destept care da o valoare default daca nu gaseste cheia

sys.setrecursionlimit(10000)
UNASSIGNED = -1  #inseamna ca o variabila inca nu a primit o valoare
FALSE = 0  #valoarea pt FALS
TRUE = 1  #valoarea pt ADEVARAT

dpll_step_count=0
dp_step_count=0
resolution_step_count=0
#-----Functie pentru citirea fisierului de intrare (format DIMACS)-----
def read_dimacs_file(filename):
    """Citeste un fisier DIMACS.
    Returneaza o lista de clauze si numarul total de variabile.
    """
    clauses=[]
    max_var=0 #cea mai mare variabila gasita in fisier
    with open(filename,'r') as f:
        for line in f:
            line=line.strip() #stergem spatiile goale de la inceputul si sfarsitul liniei
            if not line or line[0]=='c' or line[0]=='p': #sarim peste liniile care sunt comentarii (cu 'c') sau linia de 'p cnf ...'
                continue
            tokens=line.split() #impartim linia in "token-uri"-numerele care formeaza clauza
            lits=[int(x) for x in tokens if x!='0'] #convertim fiecare token intr-un numar intreg,ignorand acel '0' de la sfarsitul liniei
            if lits:
                clauses.append(lits)  #adaugam clauza la lista noastra
                max_var=max(max_var,max(abs(l) for l in lits)) #verificam daca am gasit o variabila mai mare decat ce stiam pana acum
    return clauses,max_var  #returnam lista de clauze si numarul de variabile

#-----Functie pentru initializarea "watcher-ilor" (pentru DPLL)-----
def init_watchers(clauses):
    """Pregateste sistemul de "two-watched literals" (doi literali urmariti per clauza).
    Acesta e o metoda destepata cu care verificam mai repede daca o clauza e satisfacuta.
    Returneaza:
        watchers: un dictionar care mapeaza indexul clauzei la cei doi literali urmariti.
        watch_list: un dictionar care mapeaza un literal la o lista de clauze care il urmaresc.
    """
    watchers={}
    watch_list={}
    #Functie care adauga un literal la lista de urmarire
    def add_watcher(lit,idx):
        if lit not in watch_list:
            watch_list[lit]=set() #daca literalul nu e deja in dictionar il adaugam cu un set gol
        watch_list[lit].add(idx) #adaugam indexul clauzei la setul de clauze urmarite de acest literal

    for idx,clause in enumerate(clauses):
        if len(clause)==1:
            w1=w2=clause[0]  #daca clauza are un singur literal, ambii sunt acelasi literal
        else:
            w1,w2=clause[0],clause[1]
        watchers[idx]=[w1,w2]
        #adaugam legaturile in watch_list
        add_watcher(w1,idx)
        add_watcher(w2,idx)
    return watchers,watch_list

#-----Strategii pentru a alege urmatoarea variabila(folosita la DPLL)-----
class VariableSelectionStrategies:
    """Contine diferite strategii pentru a decide ce variabila sa incercam sa setam.
    Alegerea buna a variabilei influenteaza eficienta algoritmului
    """
    @staticmethod  #inseamna ca functia apartine clasei, nu unui obiect specific
    def first_unassigned(assignment,clauses):
        """Cea mai simpla strategie: alege prima variabila care inca nu are o valoare."""
        for v_idx in range(1,len(assignment)):
            if assignment[v_idx]==UNASSIGNED:
                return v_idx  #daca variabila v_idx nu are valoare o returnam pe ea
        return None

    @staticmethod
    def highest_frequency(assignment,clauses):
        """Alege variabila care apare de cele mai multe ori in clauzele nesatisfacute."""
        freq=defaultdict(int)  #un dictionar care numara de cate ori apare fiecare variabila
        for clause in clauses:  #mergem prin fiecare clauza
            #verificam daca aceasta clauza e deja satisfacuta sau nu e relevanta
            for lit in clause:
                var=abs(lit)  #luam variabila (fara semn)
                if assignment[var]==UNASSIGNED:  #daca variabila nu are valoare
                    freq[var]+=1  #crestem contorul ei
        if not freq:  #daca nu am gasit nicio variabila neatribuita in clauze
            return None
        return max(freq.items(), key=lambda item: item[1])[0] #returnam variabila care a aparut de cele mai multe ori

    @staticmethod
    def random_choice(assignment, clauses):
        """Alege la intamplare o variabila care inca nu are o valoare."""
        #facem o lista cu toate variabilele care nu au fost atribuite
        unassigned_vars=[v_idx for v_idx in range(1,len(assignment)) if assignment[v_idx]==UNASSIGNED]
        if unassigned_vars:  #daca exista variabile neatribuite
            return random.choice(unassigned_vars)  #alegem una la intamplare
        return None

#-----Functia de propagare a constrangerilor folosind "two-watched literals"-----
def propagate(assignment, clauses, watchers, watch_list, lit_assigned):
    """Foloseste tehnica "two-watched literals" pentru eficienta.
    Returneaza True daca nu apare niciun conflict, False daca apare o contradictie.
    """
    global dpll_step_count
    stack=[lit_assigned] #punem literalul proaspat atribuit intr-o "stiva" de procesare
    while stack: #cat timp mai avem literali de procesat pe stiva
        current_lit=stack.pop()  #luam un literal de pe stiva
        opposite_lit=-current_lit
        #folosim list() pentru a copia setul, deoarece s-ar putea sa modificam watch_list[opposite_lit] in bucla
        clauses_watching_opposite=list(watch_list.get(opposite_lit,set()))
        for clause_idx in clauses_watching_opposite:
            dpll_step_count+=1
            w1,w2=watchers[clause_idx] #luam cei doi "watchers" ai clauzei curente
            other_watcher=w2 if w1==opposite_lit else w1
            found_new_watcher_for_opposite=False  #ca sa stim daca am gasit un nou watcher
            #incercam sa gasim un nou literal in clauza, pe care sa-l punem ca watcher in locul lui `opposite_lit`
            for new_potential_watcher in clauses[clause_idx]:
                #un watcher nou trebuie sa nu fie `other_watcher` si trebuie sa poata fi ADEVARAT (adica ori e neatribuit, ori e deja atribuit la o valoare care satisface literalul)
                can_be_true = (assignment[abs(new_potential_watcher)]==UNASSIGNED or
                               (new_potential_watcher>0 and assignment[abs(new_potential_watcher)]==TRUE) or
                               (new_potential_watcher<0 and assignment[abs(new_potential_watcher)]==FALSE))
                if new_potential_watcher!=other_watcher and can_be_true: #cand am gasit un nou watcher, actualizam structurile
                    if w1==opposite_lit: #daca w1 era cel pe care il schimbam
                        watchers[clause_idx][0]=new_potential_watcher
                    else: #altfel, w2 era cel pe care il schimbam
                        watchers[clause_idx][1]=new_potential_watcher
                    watch_list[opposite_lit].remove(clause_idx) #scoatem clauza din lista celor urmarite de `opposite_lit`
                    if new_potential_watcher not in watch_list:
                        watch_list[new_potential_watcher]=set() #si o adaugam la lista celor urmarite de `new_potential_watcher`
                    watch_list[new_potential_watcher].add(clause_idx)
                    found_new_watcher_for_opposite=True
                    break  #trecem la urmatoarea clauza din `clauses_watching_opposite`

            if not found_new_watcher_for_opposite:
                #daca nu am gasit un nou watcher pentru `opposite_lit` inseamna ca `other_watcher` trebuie sa faca clauza adevarata
                val_other_watcher=assignment[abs(other_watcher)]
                sign_other_watcher=TRUE if other_watcher>0 else FALSE
                if val_other_watcher==UNASSIGNED:
                    assignment[abs(other_watcher)]=sign_other_watcher #daca `other_watcher` e neatribuit, el devine obligatoriu (propagare unitara)
                    stack.append(other_watcher) #adaugam acest nou literal atribuit pe stiva de procesare
                elif val_other_watcher!=sign_other_watcher: #contradictie
                    return False
    return True

#-----Algoritmul DPLL-----
def dpll(assignment, level, clauses, var_strategy, watchers, watch_list):
    """Algoritmul DPLL principal-recursiv
    `assignment`: starea curenta a atribuirilor de variabile (o lista)
    `level`: nivelul de recursie (nu e folosit explicit aici, dar e bun pentru debug/euristici avansate)
    `clauses`: lista de clauze originala
    `var_strategy`: functia folosita pentru a alege urmatoarea variabila de testat
    `watchers`, `watch_list`: structurile pentru two-watched literals
    """
    var_to_assign=var_strategy(assignment,clauses) #alegem o variabila folosind strategia data
    if var_to_assign is None:  # Daca nu mai sunt variabile de ales (conform strategiei)
        # Verificam daca toate clauzele sunt satisfacute de atribuirea curenta. Daca sunt, am gasit o solutie
        for clause in clauses:
            is_clause_satisfied=False
            for lit_in_clause in clause:
                var_of_lit=abs(lit_in_clause)
                val_of_var=assignment[var_of_lit]
                if (lit_in_clause>0 and val_of_var==TRUE) or \
                        (lit_in_clause<0 and val_of_var==FALSE):
                    is_clause_satisfied=True
                    break  #clauza e satisfacuta, trecem la urmatoarea
            if not is_clause_satisfied:
                return False  #am gasit o clauza nesatisfacuta, deci aceasta ramura a esuat
        return True  #toate clauzele sunt satisfacute!

    #incercam sa atribuim TRUE si FALSE pentru variabila aleasa
    for value_to_try in (TRUE,FALSE):
        #facem o copie a starii curente, ca sa putem reveni daca aceasta ramura esueaza
        original_assignment_copy=assignment[:]
        watchers_copy={k: list(v) for k,v in watchers.items()}
        watch_list_copy={k: set(v) for k,v in watch_list.items()}
        assignment[var_to_assign]=value_to_try  #facem atribuirea de test
        lit_that_was_assigned=var_to_assign if value_to_try==TRUE else -var_to_assign
        #propagam consecintele acestei atribuiri
        if propagate(assignment, clauses, watchers, watch_list, lit_that_was_assigned):
            #daca propagarea nu a dus la un conflict, continuam recursiv
            if dpll(assignment, level + 1, clauses, var_strategy, watchers, watch_list):
                return True  #am gasit o solutie pe aceasta ramura
        #daca am ajuns aici, inseamna ca fie propagarea a dat contradictie => trebuie sa revenim la starea de dinainte de a incerca `value_to_try`.
        assignment[:] = original_assignment_copy
        watchers.clear();
        watchers.update(watchers_copy)
        watch_list.clear();
        watch_list.update(watch_list_copy)
    return False  #am incercat si TRUE si FALSE pentru `var_to_assign` si ambele ramuri au esuat
#-----Functie ajutatoare pentru algoritmul DP-----
def simplify_clauses_by_assignment(clauses, assignment):
    """Primeste o lista de clauze si o atribuire partiala.
    Returneaza o noua lista de clauze simplificate:
        - Clauzele satisfacute de atribuire sunt eliminate.
        - Literalii falsi sunt eliminati din clauzele ramase.
    Returneaza (lista_clauze_simplificate, a_aparut_conflict).
    Conflictul apare daca o clauza devine vida.
    """
    simplified_clauses_list=[]
    for c in clauses:
        new_clause=[]  # Clauza curenta, dupa simplificare
        is_original_clause_satisfied=False
        for literal in c:
            var=abs(literal)
            val_of_var=assignment[var]
            if val_of_var==UNASSIGNED:  #daca variabila literalului e neatribuita pastram literalul in noua clauza
                new_clause.append(literal)
            elif (literal>0 and val_of_var==TRUE) or (literal<0 and val_of_var==FALSE):

                is_original_clause_satisfied=True #literalul este ADEVARAT in atribuirea curenta, deci clauza originala e satisfacuta
                break
        if not is_original_clause_satisfied:  #daca clauza originala nu a fost satisfacuta de atribuire
            if not new_clause:  #daca clauza ,dupa eliminarea literalilor falsi este vida
                return None,True  #contradictie, am derivat o clauza vida.
            simplified_clauses_list.append(new_clause)  #adaugam clauza simplificata la rezultat
    return simplified_clauses_list,False  #returnam clauzele simplificate si ca nu a fost conflict

#-----Algoritmul Davis-Putnam (varianta simplificata)-----
def davis_putnam_solver(current_clauses_list,assignment,num_total_vars):
    """O implementare a algoritmului Davis-Putnam
    Nu e varianta originala DP cu eliminare de variabile prin rezolutie, dar una care seamana mai mult cu DPLL ca structura( aplica regulile DP iterativ)
    """
    global dp_step_count
    clauses_to_process = [list(c) for c in current_clauses_list] #facem o copie cu care sa lucram, ca sa nu modificam lista originala intre apeluri recursive
    #aplicam propagarea unitara si regula literalului pur pana nu se mai schimba nimic
    while True:
        #Pas 1: Simplificam clauzelee
        clauses_after_simplification,conflict_occured=simplify_clauses_by_assignment(clauses_to_process,assignment)
        if conflict_occured:return False
        if not clauses_after_simplification:return True
        clauses_to_process = clauses_after_simplification  #actualizam setul de clauze

        #Pas 2: Propagare Unitara
        unit_propagation_made_change=False
        for clause in clauses_to_process:
            if len(clause)==1:  #am gasit o clauza unitara
                unit_literal=clause[0]
                var_of_unit=abs(unit_literal)
                value_to_assign=TRUE if unit_literal>0 else FALSE
                if assignment[var_of_unit]==UNASSIGNED:
                    dp_step_count+=1
                    assignment[var_of_unit]=value_to_assign
                    unit_propagation_made_change=True
                    break  #restartam bucla de simplificare, deoarece o noua atribuire poate simplifica si mai mult
                elif assignment[var_of_unit] != value_to_assign:
                    return False
        if unit_propagation_made_change: continue  #daca am facut o propagare, reluam bucla de simplificare

        # Pas 3: Regula Literalului Pur
        pure_literal_made_change=False
        literal_polarities=defaultdict(lambda:[0,0])
        vars_in_current_clauses_nealocate=set()
        for clause in clauses_to_process:
            for literal in clause:
                var=abs(literal)
                if assignment[var]==UNASSIGNED:  #luam in considerare doar variabilele nealocate
                    vars_in_current_clauses_nealocate.add(var)
                    if literal>0:
                        literal_polarities[var][0]+=1 #apare pozitiv
                    else:
                        literal_polarities[var][1]+=1 #apare negativ

        for var in vars_in_current_clauses_nealocate:
            count_pos,count_neg=literal_polarities[var]
            if count_pos>0 and count_neg==0:  #literal pur pozitiv
                dp_step_count+=1
                assignment[var]=TRUE
                pure_literal_made_change=True
                break  #restartam bucla de simplificare
            elif count_neg>0 and count_pos==0:  #literal pur negativ
                dp_step_count+=1
                assignment[var]=FALSE
                pure_literal_made_change=True
                break #restartam bucla de simplificare
        if pure_literal_made_change: continue
        break  #daca am ajuns aici, nici propagarea unitara, nici regula literalului pur nu au mai adus modificari. Iesim din bucla de simplificare

    #dupa ce am simplificat cat am putut, selectam o variabila pentru "split"
    #alegem prima variabila neatribuita care inca mai apare in clauzele ramase.
    vars_to_choose_from=set()
    for cl in clauses_to_process: #ne uitam doar la clauzele care au mai ramas
        for lit in cl:
            if assignment[abs(lit)]==UNASSIGNED:
                vars_to_choose_from.add(abs(lit))
    if not vars_to_choose_from:  #daca nu mai sunt variabile neatribuite in clauzele ramase
        return not clauses_to_process  #adevarat daca lista de clauze e goala
    #alegem variabila cu indexul cel mai mic dintre cele ramase (o strategie simpla)
    var_to_split_on=min(vars_to_choose_from)
    dp_step_count+=1
    for value_choice in (TRUE,FALSE): #incercam ambele valori pentru variabila aleasa
        assignment_for_branch=assignment[:]  #copie pentru aceasta ramura
        assignment_for_branch[var_to_split_on]=value_choice
        if davis_putnam_solver(list(clauses_to_process),assignment_for_branch,num_total_vars): #apelam recursiv, cu o copie a listei de clauze procesate pana acum
            #daca o ramura a gasit o solutie, actualizam atribuirea originala si returnam Adevarat
            for i in range(len(assignment)):assignment[i]=assignment_for_branch[i]
            return True
    return False
#-------------------Algoritmul de Rezolutie-------------------
def resolution_solver(initial_clauses_list,num_vars):
    """Implementeaza algoritmul de rezolutie.
    Incearca sa derive clauza vida. Daca reuseste, formula e NESATISFIABILA.
    Daca nu mai poate genera clauze noi fara clauza vida, e SATISFIABILA.
    """
    global resolution_step_count
    resolution_step_count=0
    #folosim `frozenset` pentru clauze, ca sa le putem pune intr-un set
    clauses_set={frozenset(c) for c in initial_clauses_list}
    if frozenset() in clauses_set:  #daca formula contine din start clauza vida, e nesatisfiabila
        return False

    #limite pentru a opri algoritmul daca devine prea lent sau consuma prea multa memorie
    MAX_ITERATIONS_OVER_SET=500
    MAX_TOTAL_CLAUSES=10000
    current_iteration=0

    while current_iteration<MAX_ITERATIONS_OVER_SET and len(clauses_set)<MAX_TOTAL_CLAUSES:
        current_iteration+=1
        newly_derived_this_pass=set()  #ttine minte rezolventii noi din iteratia curenta
        list_of_current_clauses = list(clauses_set) #convertim setul de clauze intr-o lista, la fiecare iteratie, deoarece `clauses_set` se modifica.
        for i in range(len(list_of_current_clauses)):  #incercam sa rezolvam fiecare pereche de clauze
            for j in range(i+1,len(list_of_current_clauses)):  # j > i ca sa evitam perechi duplicate
                c1=list_of_current_clauses[i]
                c2=list_of_current_clauses[j]
                #incercam sa gasim un literal L in C1 astfel incat -L sa fie in C2
                for literal_from_c1 in c1:
                    if -literal_from_c1 in c2:  #am gasit o pereche de literali opusi
                        resolvent=(c1-{literal_from_c1}) | (c2-{-literal_from_c1})
                        resolution_step_count+=1
                        #verificam daca rezolventul e o tautologie
                        is_tautology=False
                        for res_lit in resolvent:
                            if -res_lit in resolvent:
                                is_tautology=True
                                break
                        if is_tautology:continue  #trecem la urmatorul literal
                        if not resolvent:
                            return False  #formula este NESATISFIABILA
                        #verificare simpla de subsumare: daca rezolventul e deja incadrat de o clauza mai generala (mai mica sau egala) care exista deja, il ignoram
                        #de exemplu daca avem {a,b} si derivam {a,b,c}, {a,b,c} este inutil
                        is_subsumed=False
                        for existing_clause in clauses_set:
                            if existing_clause.issubset(resolvent):
                                is_subsumed=True
                                break
                        if is_subsumed:continue
                        if resolvent not in clauses_set and resolvent not in newly_derived_this_pass: #daca rezolventul e nou
                            newly_derived_this_pass.add(resolvent)
                        break  #trecem la urmatoarea pereche de clauze (j++ sau i++)
        if not newly_derived_this_pass:  #daca in toata aceasta tura nu am mai gasit niciun rezolvent nou
            return True  #formula e SATISFIABILA.
        #adaugam rezolventii noi derivati la setul principal de clauze
        added_at_least_one_to_main_set=False
        for r in newly_derived_this_pass:
            if r not in clauses_set: #dubla verificare, in caz ca intre timp a fost adaugat
                clauses_set.add(r)
                added_at_least_one_to_main_set=True
        if not added_at_least_one_to_main_set:  #daca toti rezolventii noi erau deja in `clauses_set`
            return True  #SATISFIABIL
    return True  #presupunem SATISFIABIL

def main():
    filename='date.txt'
    print(f"\nIncarcam formule CNF din fisierul {filename}:")
    clauses_list,num_vars=read_dimacs_file(filename)
    print(f"Numar clauze: {len(clauses_list)}")
    print(f"Numar variabile: {num_vars}")
    #lista de strategii/algoritmi pe care ii vom testa
    strategies_to_run = [
        ("Resolution (Basic)", "RESOLUTION_ALGORITHM"),  #algoritmul de Rezolutie
        ("Davis-Putnam (DP)", "DAVIS_PUTNAM_ALGORITHM"),  #algoritmul Davis-Putnam (varianta DP-like)
        ("First Unassigned (DPLL)", VariableSelectionStrategies.first_unassigned),  #DPLL cu prima variabila
        ("Random (DPLL)", VariableSelectionStrategies.random_choice),  #DPLL cu alegere random
        ("Frequency (DPLL)", VariableSelectionStrategies.highest_frequency)  #DPLL cu frecventa cea mai mare
    ]

    #afisare
    print("\n"+"="*75)
    print(f"{'Strategy':<30} {'Satisfiable':<15} {'Time (s)':<15} {'Steps':<15}")
    print("="*75)

    #rulam fiecare strategie pe rand
    for strategy_name,strategy_logic in strategies_to_run:
        #resetam atribuirile pentru fiecare rulare (important pentru DP si DPLL)
        current_assignment=[UNASSIGNED]*(num_vars + 1)
        time_start=time.perf_counter()  # Pornim cronometrul
        run_steps_count=0
        is_satisfiable=False

        #verificam ce strategie trebuie sa rulam
        if strategy_logic=="RESOLUTION_ALGORITHM":
            global resolution_step_count
            resolution_step_count=0
            #facem o copie a listei de clauze pentru siguranta
            clauses_copy_for_res=[list(c) for c in clauses_list]
            is_satisfiable=resolution_solver(clauses_copy_for_res, num_vars)
            run_steps_count=resolution_step_count

        elif strategy_logic=="DAVIS_PUTNAM_ALGORITHM":
            global dp_step_count
            dp_step_count=0
            clauses_copy_for_dp=[list(c) for c in clauses_list]
            is_satisfiable=davis_putnam_solver(clauses_copy_for_dp, current_assignment, num_vars)
            run_steps_count=dp_step_count

        else: #altfel, e o strategie DPLL
            global dpll_step_count
            dpll_step_count=0
            #DPLL are nevoie de watchers, ii initializam pentru fiecare rulare
            watchers_struct,watch_list_struct=init_watchers(clauses_list)
            variable_selection_function=strategy_logic  #functia de selectie a variabilei
            is_satisfiable=dpll(current_assignment,1,clauses_list,variable_selection_function,watchers_struct,watch_list_struct)
            run_steps_count=dpll_step_count
        time_elapsed=time.perf_counter()-time_start  #oprim cronometrul
        print(f"{strategy_name:<30} {('YES' if is_satisfiable else 'NO'):<15} {time_elapsed:<15.6f} {run_steps_count:<15}")
    print("="*75+"\n")
if __name__=='__main__':
    main()