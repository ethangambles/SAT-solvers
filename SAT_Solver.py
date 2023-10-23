import os
import time
import random
PATH = 'PA3_Benchmarks\PA3_Benchmarks\HARD CNF Formulas\\'
VAR_PER_CLAUSE = 3
NUM_PARENTS = 6

def readFile(file):
    currentClause = 0
    with open(PATH+file, 'r') as f:
        for lines in f:
            clause = lines.split(' ')
            #HARD
            if PATH == 'PA3_Benchmarks\PA3_Benchmarks\HARD CNF Formulas\\' or PATH == 'PA3_Benchmarks\\PA3_Benchmarks\\try_cnf\\':
                if currentClause == 0:
                    fileName = file.split('.')
                    nbvar = int(fileName[0])
                    nbclauses = int(fileName[1])
                    cnf = [[0 for i in range(VAR_PER_CLAUSE)] for j in range(nbclauses)]
                
                if clause[0] == 'c' or clause[0] == 'c\n' or clause[0] == 'p' or clause[0] == '\n':
                    pass
                else:
                    for item in clause:
                        if item == '0\n' or item == '%\n' or item == '\n' or item == '':
                            pass
                        else:
                            cnf[currentClause][clause.index(item) - 1] = int(item)
                    currentClause+=1


            #NORMAL
            elif PATH == 'PA3_Benchmarks\PA3_Benchmarks\CNF Formulas\\':
                if clause[0] == 'c' or clause[0] == 'c\n':
                    pass
                elif clause[0] == 'p':
                    nbvar = int(clause[2])
                    nbclauses = int(clause[4])
                    cnf = [[0 for i in range(VAR_PER_CLAUSE)] for j in range(nbclauses)]
                else:
                    #store a 0 if variable does not appear, 1 if variable appears positively, 2 if variable appears negated
                    for item in clause:
                        if item == '0\n' or item == '%\n' or item == '\n' or item == '':
                            pass
                        else:
                            cnf[currentClause][clause.index(item) - 1] = int(item)
                    currentClause+=1
    f.close()
    return cnf, nbvar, nbclauses

def findUnitPropagation(clauses):
    for subclause in clauses:
        if len(subclause) == 1:
            unitPropagate = subclause[0]
            return unitPropagate

def findPureLiterals(clauses):
    pureLiterals = []
    allLiterals = set()
    
    # Step 1: Gather all literals and their appearances
    for clause in clauses:
        for literal in clause:
            allLiterals.add(abs(int(literal)))
    
    # Step 2: Check if a literal is pure
    for literal in allLiterals:
        appears_positive = False
        appears_negative = False
        
        for clause in clauses:
            if literal in clause:
                appears_positive = True
            if -literal in clause:
                appears_negative = True
        
        if appears_positive != appears_negative:
            pureLiterals.append(literal if appears_positive else -literal)
    return pureLiterals

def testHighestSatisfiedClauses(numSatisfiedClauses, maxSatisfiedClauses):
    if numSatisfiedClauses > maxSatisfiedClauses:
        return numSatisfiedClauses
    else:
        return maxSatisfiedClauses

def isClauseSatisfied(clause, assignment):
    for literal in clause:
        if literal > 0 and assignment[abs(literal)-1] or literal < 0 and not assignment[abs(literal)-1]:
            return True
    return False

def allClausesSatisfied(clauses, assignment):
    for subclause in clauses:
        if not isClauseSatisfied(subclause, assignment):
            return False
    return True

def getNumSatisfiedClauses(clauses,assignment):
    count = 0
    for subclause in clauses:
        if isClauseSatisfied(subclause, assignment):
            count+=1
    return count


def WalkSAToptimalVariable(clauses, clause, assignment):
    bestVariable = None
    mostSatisfied = 0
    for literal in clause:
        variable = abs(literal)
        assignment[variable-1] = not assignment[variable-1] #flip variable
        numSatisfied = sum(1 for subclause in clauses if isClauseSatisfied(subclause, assignment))
        assignment[variable-1] = not assignment[variable-1] #return variable to original value

        if numSatisfied > mostSatisfied:
            mostSatisfied = numSatisfied
            bestVariable = variable
    return bestVariable

def evaluateFitness(clauses, population):
    #initial population is list of randomly assigned literals (a truth assignment equation), and their fitness is how many clauses they satisfy
    fitness = 0
    for clause in clauses:
        if isClauseSatisfied(clause, population):
            fitness +=1
    return fitness  #make fitness how many clauses are satisfied

def chooseParents(populations):
    fitness_sum = sum(individual[1] for individual in populations)
    probabilities = [individual[1] / fitness_sum for individual in populations]

    parents = random.choices(populations, probabilities, k=NUM_PARENTS) #select parents based on fitness - higher fitness has more probability
    return parents


def reproduce(parent1, parent2, numVariables):
    child = []
    for i in range(numVariables // 2): #take randomly from parent 1
        child.append(random.choice(parent1[0]))
    for i in range(numVariables // 2): #take the second half of the second parent
        child.append(random.choice(parent2[0]))
    return child

    
def dpll(clauses, satisfiedForumla, numSatisfied):
        #Unit propogation
        while True:
            unitPropagate = findUnitPropagation(clauses)
            if unitPropagate:
                clauses = [subclause for subclause in clauses if unitPropagate not in subclause] #take out all clauses containing the unit propagation

                clauses = [[item for item in subclause if item != -unitPropagate] for subclause in clauses] #remove the negation of the unit propagation, as now it will be false and cannot help the clause
                if unitPropagate < 0:
                   satisfiedForumla[abs(unitPropagate) - 1] = False
                else:
                    satisfiedForumla[unitPropagate - 1] = True
            else:
                break

        #pure literal propagation
        while True:
            pureLiterals = findPureLiterals(clauses)
            if pureLiterals:
                while pureLiterals:
                    literal = pureLiterals.pop()
                    clauses = [subclause for subclause in clauses if literal not in subclause] #remove any clauses with a pure literal
                    if literal < 0:
                        satisfiedForumla[abs(literal) - 1] = False
                    else:
                        satisfiedForumla[literal - 1] = True

            else:
                break
        
        if not clauses: #if no more clauses, return True
            return True

        for subclause in clauses: #if there is an empty clause (clause that cannot be true) return False
            if len(subclause) == 0:
                return False

        numSatisfied[0] = getNumSatisfiedClauses(clauses, satisfiedForumla)
        chooseLiteral = clauses[0][0] #choose first literal

        return dpll(clauses + [[chooseLiteral]], satisfiedForumla, numSatisfied) or dpll(clauses + [[-chooseLiteral]], satisfiedForumla, numSatisfied)



def geneticAlg(clauses, numVariables):
    maxUnchangedGenerations = 100
    populations = []
    newPopulation = []
    maxResets = 5
    initialPopulation = 200
    overallBestFitness = 0
    previousBestFitness = 0
    
    for _ in range(maxResets):
        populations.clear()
        if previousBestFitness > overallBestFitness:
            overallBestFitness = previousBestFitness
        cnt = 0
        previousBestFitness = 0
        #initilaize populations
        for _ in range(initialPopulation):
            population = [random.choice([True,False]) for _ in range (numVariables)]
            populations.append((population, evaluateFitness(clauses, population)))

        while cnt < maxUnchangedGenerations: #if fitness does not change for a number of generations, reset
                populations = sorted(populations, key=lambda x: x[1], reverse=True) #sort list by fitness, bringing largest fitness to front
                bestIndividual = populations[0] #Elitism

                if previousBestFitness < bestIndividual[1]:
                    previousBestFitness = bestIndividual[1]
                    cnt = 0
                else:
                    cnt+=1

                #CULL
                for _ in range(NUM_PARENTS):#cull as many as will be produced
                    populations.pop()

                newPopulation.clear()
        
                if bestIndividual[1] == len(clauses): #if all clauses satisfied return True
                    return True, bestIndividual[1], bestIndividual[0]
                
                #REPRODUCE
                newPopulation.append(bestIndividual)
                while len(newPopulation) < initialPopulation:
                    parents = chooseParents(populations)
                    for j in range(NUM_PARENTS - 1):
                        child = reproduce(parents[j], parents[j+1], numVariables)
                        #MUTATE with 4% probability
                        p = random.choice(range(0,100))
                        if p <= 4:
                            randIndex= random.choice(range(numVariables))
                            child[randIndex] = not child[randIndex]
                        newPopulation.append((child, evaluateFitness(clauses, child)))
                
                
                populations.clear()
                populations = newPopulation
    if previousBestFitness > overallBestFitness:
        overallBestFitness = previousBestFitness
    return False, overallBestFitness
    

def WalkSAT(clauses, numVariables):
    #initalize a by randomly assigning values
    random_assignment = [0 for i in range(numVariables)]
    mostSatisfied = 0
    testMostSatisfied = 0

    max_flips = numVariables*3 #timeout condition
    for _ in range(100): # max of 100 restarts
        for i in range(numVariables):
            random_assignment[i] = random.choice([True,False])
        for _ in range(max_flips):

            if allClausesSatisfied(clauses, random_assignment):
                return True, mostSatisfied, random_assignment
            
            p = random.choice(range(100))
            randomClause = random.choice(clauses)
            while isClauseSatisfied(randomClause, random_assignment): #get a random unsatisfied clause
                randomClause = random.choice(clauses)
            
            if p < 65:
                flip = WalkSAToptimalVariable(clauses, randomClause, random_assignment) #find the variable that, if flipped, satisfies the most clauses
                random_assignment[flip-1]  = not random_assignment[flip-1]
                testMostSatisfied = getNumSatisfiedClauses(clauses, random_assignment)
                mostSatisfied = testHighestSatisfiedClauses(testMostSatisfied, mostSatisfied)
            else:
                flip = random.choice(randomClause)
                random_assignment[abs(flip)-1] = not random_assignment[abs(flip)-1]
                testMostSatisfied = getNumSatisfiedClauses(clauses, random_assignment)
                mostSatisfied = testHighestSatisfiedClauses(testMostSatisfied, mostSatisfied)
    return False, mostSatisfied

if __name__ == '__main__':
    #WalkSAT
    for file in os.listdir(PATH):
        file_extension = os.path.splitext(file)[1]
        if file_extension == '.cnf':
            print("Running WalkSAT on", file)
            clauses, numVariables, numClauses = readFile(file)
            startTime = time.time()
            for i in range(10):
                startTime = time.time()
                w = WalkSAT(clauses,numVariables)
                endTime = time.time()
                totalTime = endTime - startTime
                if w[0]:
                    with open('walksat_output.txt', 'a') as f:
                        f.writelines(file + " was found satisfiable in "+ str(totalTime) +" seconds with the highest c being " + str(w[1]) + " and the satisfied formula "+ str(w[2]) + '\n')
                    
                else:
                    with open('walksat_output.txt', 'a') as f:
                        f.writelines(file + " timed out after " + str(totalTime) + " seconds and the highest c was " + str(w[1]) + ".\n")
                print('Done with iteration',i + 1)

    #DPLL
    for file in os.listdir(PATH):
        file_extension = os.path.splitext(file)[1]
        if file_extension == '.cnf':
            print("Running DPLL on", file)
            clauses, numVariables, numClauses = readFile(file)
            satisfiedFormula = [False for i in range(numVariables)]
            satisfiedClauses = [0]
            startTime = time.time()
            d = dpll(clauses, satisfiedFormula, satisfiedClauses)
            endTime = time.time()
            totalTime = endTime - startTime
            if d:
                with open('dpll_output.txt', 'a') as f:
                    f.writelines(file + " was found satisfiable in "+ str(totalTime) +" seconds with the highest c being " + str(numClauses) + " and the satisfied formula "+ str(satisfiedFormula) + '\n')
                
            else:
                with open('dpll_output.txt', 'a') as f:
                    f.writelines(file + " was found  not satisfiable in " + str(totalTime) + " seconds and the highest c being " + str(satisfiedClauses[0]) +".\n")
            print('Done')

    #GENETIC ALGORITHM
    for file in os.listdir(PATH):
        file_extension = os.path.splitext(file)[1]
        if file_extension == '.cnf':
            print("Running Genetic Algorithm on", file)
            clauses, numVariables, numClauses = readFile(file)
            for i in range(10):
                startTime = time.time()
                g = geneticAlg(clauses, numVariables)
                endTime = time.time()
                totalTime = endTime - startTime
                if g[0]:
                    with open('GA_output.txt', 'a') as f:
                        f.writelines(file + " was found satisfiable in "+ str(totalTime) +" seconds with the highest c being " + str(g[1]) + " and the satisfied formula "+ str(g[2]) + '\n')
                    
                else:
                    with open('GA_output.txt', 'a') as f:
                        f.writelines(file + " timed out after " + str(totalTime) + " seconds and the highest c was " + str(g[1]) + ".\n")
                print('Done with iteration',i + 1)



            