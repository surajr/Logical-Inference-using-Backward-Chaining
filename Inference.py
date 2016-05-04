import sys,getopt
import re

visited=[]
ob='('
cb=')'
operators = ['&&', '=>']

class KB:
    def __init__(self):
        self.clauses = {}

    def tell(self, clause):
        index_clauses(self,clause, clause)

    def ask(self, query):
        return FOL_BC_ASK(self, query)

class Statement:
    def __init__(self, op, args = []):
        self.op = op
        self.args = map(make_class_statement, args)

    def __repr__(self):
        if len(self.args) == 0:
            self_op=self.op
            return self_op
        elif self.op not in operators:
            args = str(self.args[0])
            for arg in self.args[1:]:
                args = args + ', ' + str(arg)
            temp= self.op + ob + args + cb
            return temp

    def __hash__(self):
        temp=hash(self.op) ^ hash(tuple(self.args))
        return  temp

    def __eq__(self, other):
        return isinstance(other, Statement) and self.op == other.op and \
        self.args == other.args

def FOL_BC_ASK(kb, query):
    return FOL_BC_OR(kb, query, {})


def FOL_BC_OR(kb, goal, theta):

    if goal in visited:
        return
    visited.append(goal)
    print "Ask: ", SUBST(theta,goal)
    nextwrite.write("Ask: " + str(SUBST(theta,goal)) + "\n")

    rules_for_goal = fetch_rules_for_goal(kb,goal)
    for rule in rules_for_goal:
        standardized_rule = STANDARDIZE_VARIABLES(rule)
        lhs, rhs = lhs_rhs(standardized_rule)
        unify_solution = UNIFY(rhs, goal, theta)

        for thetadash in FOL_BC_AND(kb, lhs, unify_solution):
            #print "thetadash", SUBST(thetadash,goal)
            if goal in visited:
                print "True: ", SUBST(thetadash,goal)
                nextwrite.write("True: " + str(SUBST(thetadash,goal)) + "\n")
                visited.remove(goal)
            else:
                nextwrite.write("True: " + str(SUBST(thetadash,goal)) + "\n")
                print "True: ", SUBST(thetadash,goal)

            yield thetadash
    if goal in visited:
        print "False:", SUBST(theta,goal)
        nextwrite.write("False: " + str(SUBST(theta,goal)) + "\n")
        visited.remove(goal)
        if len(visited)!=0:
            x = visited.pop()
            print "Ask: ", SUBST(theta,x)
            nextwrite.write("Ask: " + str(SUBST(theta,x)) + "\n")



temp_list = []
def FOL_BC_AND(kb, goals, theta):
    if theta is None:
        pass
    elif isinstance(goals, list) and len(goals) == 0:
        yield theta
    else:
        if goals.op == '&&':
            first = goals.args[0]
            second = goals.args[1]
            if first.op == '&&':
                while not is_predicate(first):
                    firstarg=first.args[1]
                    secondarg=second
                    temp=[firstarg,secondarg ]
                    second = Statement('&&',temp )
                    first = first.args[0]
        else:
            first = goals
            second = []
        for thetadash in FOL_BC_OR(kb, SUBST(theta, first), theta):
            for thetaddash in FOL_BC_AND(kb, second, thetadash):
                if goals in visited:
                    visited.remove(goals)

                yield thetaddash





def is_predicate(clause):
        if clause.op not in operators and clause.op[0].isupper():
            return True
        else:
            return False

def is_variable(clause):
    if isinstance(clause, Statement) and clause.op.islower() and clause.args == []:
        return True
    else:
        return False

def SUBST(theta, clause):
    if(isinstance(clause, Statement)):
        if is_variable(clause):
            if clause in theta:
                temp=theta[clause]
                return temp
            else:
                return clause
        else:
            temp=Statement(clause.op, (SUBST(theta, arg) for arg in clause.args))
            return temp
    else:
        return

def UNIFY(x, y, theta):

    if theta is None:

        return None
    elif x == y:

        return theta
    elif is_variable(x):
        temp=UNIFY_VAR(x, y, theta)

        return temp
    elif is_variable(y):
        temp=UNIFY_VAR(y, x, theta)

        return temp
    elif isinstance(x, Statement) and isinstance(y, Statement):
        temp1=UNIFY(x.op, y.op, theta)
        temp=UNIFY(x.args, y.args,temp1 )
        if temp is visited:
            print "unify"
        return temp
    elif isinstance(x, list) and isinstance(y, list) and len(x) == len(y):
        temp1=UNIFY(x[0], y[0], theta)
        temp=UNIFY(x[1:], y[1:], temp1)

        return temp
    else:
        return None

def UNIFY_VAR(var, x, theta):
    if var in theta:
        thetavar=theta[var]
        temp=UNIFY(thetavar, x, theta)

        return temp
    else:
        theta_copy = theta.copy()
        theta_copy[var] = x

        return theta_copy

def index_clauses_predicate(kb,precedent,antecedent):
    if antecedent.op in kb.clauses:
        if precedent not in kb.clauses[antecedent.op]:
            kb.clauses[antecedent.op].append(precedent)
    else:
        kb.clauses[antecedent.op] = [precedent]

def index_clauses(kb, precedent, antecedent):
    if is_predicate(antecedent):
        index_clauses_predicate(kb,precedent,antecedent)

    elif antecedent.op=='=>' or antecedent.op=='&&':
        index_clauses(kb,precedent, antecedent.args[0])
        index_clauses(kb,precedent, antecedent.args[1])


def fetch_rules_for_goal(kb, goal):
    all_clauses = []
    try:
        predicate = getclause(kb,goal)
        if predicate in kb.clauses:
            temp=kb.clauses[predicate]
            return temp
    except:
        for key in kb.clauses.keys():
            all_clauses =all_clauses + kb.clauses[key]
        temp=set(all_clauses)
        temp1=list(temp)
        return temp1

def getclause(kb, goal):
    if is_predicate(goal):
        goal_op=goal.op
        return goal_op
    else:
        firstarg=goal.args[0]
        temp=getclause(kb,firstarg)
        return temp

def imp_func(clause):
    implication_index = clause.index('=>')
    lhs = clause[:implication_index]
    rhs = clause[implication_index + 1:]
    value=[lhs, rhs]
    return Statement('=>',value )

def and_func(clause):
    and_index = clause.index('&&')
    lhs = clause[:and_index]
    rhs = clause[and_index + 1:]
    value=[lhs, rhs]
    return Statement('&&', value)

def make_class_statement(clause):
    if isinstance(clause, Statement):
        return clause
    if '=>' in clause:
        temp=imp_func(clause)
        return temp
    elif '&&' in clause:
        temp= and_func(clause)
        return temp
    elif isinstance(clause, str):
        return Statement(clause)
    first=clause[0]
    last=clause[1:][0]
    temp=Statement(first,last)
    return temp

def lhs_conversion(clause):
    if clause.op =='&&':
        first = lhs_conversion(clause.args[0])
        last = lhs_conversion(clause.args[1])
        value1= [first, last]
        value=Statement(clause.op,value1)
        return value
    else:
       return clause

Counterflag=0
def STANDARDIZE_VARIABLES(clause, standardized = None):
    global Counterflag
    if standardized is None:
        standardized = {}
    if not isinstance(clause, Statement):
        return clause
    if is_variable(clause):
        if clause in standardized:
            temp=standardized[clause]
            return temp
        else:
            strcf=str(Counterflag)
            temp = Statement('x_' +strcf )
            Counterflag = Counterflag+ 1
            standardized[clause] = temp
            return temp
    else:
        temp=Statement(clause.op, (STANDARDIZE_VARIABLES(arg, standardized) for arg in clause.args))
        return temp

def lhs_rhs(clause):
    if clause.op == '=>':
        arg1=clause.args[0]
        temp=lhs_conversion(arg1)
        temp1=clause.args[1]
        return temp, temp1
    else:
        emptylist=[]
        return emptylist, clause


def function_parsing(clause):
    clause = '(' + clause + ')'
    clause = clause.replace('(', ' ( ')
    clause = clause.replace(')', ' ) ')
    clause = clause.replace(',', ' ')

    statement1=clause
    clause = statement1.split()
    return clause

def parse_input(clause):
    value=function_parsing(clause)
    return make_clause_to_list(value)


def make_clause_to_list(clause):
    temp1=clause.pop(0)
    first = temp1
    if temp1 == ob:
        temp = []
        while clause[0] != cb:
            tempy=make_clause_to_list(clause)
            temp.append(tempy)
        tempz=clause.pop(0)
        return temp
    else:
        return first



#MAIN

f=open(sys.argv[-1], 'r')
nextwrite = open('output.txt', 'w+')
queries=[]
clauses=[]
query=[]

query = (f.readline().strip())
queries = query.split('&&')
print queries
noOfClauses=int(f.readline().strip())
#print noOfClauses

for i in range(0,noOfClauses):
    clauses.append(f.readline().strip())
#print clauses
#print queries
kb=KB()

#raw_input()


for i in range(0,len(clauses)):
    x=make_class_statement(parse_input(clauses[i]))
    kb.tell(x)

visited=[]
Counterflag=0

flag = False
result=True
for i in range(0,len(queries)):
    temp = kb.ask(make_class_statement(parse_input(queries[i])))
    try:
        ans_list = next(temp)
        flag = True
    except StopIteration:
        flag=False

if flag:
    print "True"
    nextwrite.write("True"+"\n")

else:
    print "False"
    nextwrite.write("False"+"\n")

nextwrite.close()

f = open('output.txt','r')
filedata = f.read()
f.close()

f = open('output.txt','w')
ret = re.sub("x(_\d+)?", "_",filedata)
f.write(ret)


f.close()



#END MAIN