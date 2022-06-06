import streamlit as st
import streamlit.components.v1 as components

def removeLeftRecursion(rulesDiction):
	# for rule: A->Aa|b
	# result: A->bA',A'->aA'|#

	# 'store' has new rules to be added
	store = {}
	# traverse over rules
	for lhs in rulesDiction:
		# alphaRules stores subrules with left-recursion
		# betaRules stores subrules without left-recursion
		alphaRules = []
		betaRules = []
		# get rhs for current lhs
		allrhs = rulesDiction[lhs]
		for subrhs in allrhs:
			if subrhs[0] == lhs:
				alphaRules.append(subrhs[1:])
			else:
				betaRules.append(subrhs)
		# alpha and beta containing subrules are separated
		# now form two new rules
		if len(alphaRules) != 0:
			# to generate new unique symbol
			# add ' till unique not generated
			lhs_ = lhs + "'"
			while (lhs_ in rulesDiction.keys()) \
					or (lhs_ in store.keys()):
				lhs_ += "'"
			# make beta rule
			for b in range(0, len(betaRules)):
				betaRules[b].append(lhs_)
			rulesDiction[lhs] = betaRules
			# make alpha rule
			for a in range(0, len(alphaRules)):
				alphaRules[a].append(lhs_)
			alphaRules.append(['#'])
			# store in temp dict, append to
			# - rulesDiction at end of traversal
			store[lhs_] = alphaRules
	# add newly generated rules generated
	# - after removing left recursion
	for left in store:
		rulesDiction[left] = store[left]
	return rulesDiction


def LeftFactoring(rulesDiction):
	# for rule: A->aDF|aCV|k
	# result: A->aA'|k, A'->DF|CV

	# newDict stores newly generated
	# - rules after left factoring
	newDict = {}
	# iterate over all rules of dictionary
	for lhs in rulesDiction:
		# get rhs for given lhs
		allrhs = rulesDiction[lhs]
		# temp dictionary helps detect left factoring
		temp = dict()
		for subrhs in allrhs:
			if subrhs[0] not in list(temp.keys()):
				temp[subrhs[0]] = [subrhs]
			else:
				temp[subrhs[0]].append(subrhs)
		# if value list count for any key in temp is > 1,
		# - it has left factoring
		# new_rule stores new subrules for current LHS symbol
		new_rule = []
		# temp_dict stores new subrules for left factoring
		tempo_dict = {}
		for term_key in temp:
			# get value from temp for term_key
			allStartingWithTermKey = temp[term_key]
			if len(allStartingWithTermKey) > 1:
				# left factoring required
				# to generate new unique symbol
				# - add ' till unique not generated
				lhs_ = lhs + "'"
				while (lhs_ in rulesDiction.keys()) \
						or (lhs_ in tempo_dict.keys()):
					lhs_ += "'"
				# append the left factored result
				new_rule.append([term_key, lhs_])
				# add expanded rules to tempo_dict
				ex_rules = []
				for g in temp[term_key]:
					ex_rules.append(g[1:])
				tempo_dict[lhs_] = ex_rules
			else:
				# no left factoring required
				new_rule.append(allStartingWithTermKey[0])
		# add original rule
		newDict[lhs] = new_rule
		# add newly generated rules after left factoring
		for key in tempo_dict:
			newDict[key] = tempo_dict[key]
	return newDict


# calculation of first
# epsilon is denoted by '#' (semi-colon)

# pass rule in first function
def first(rule):
	global rules, nonterm_userdef, \
		term_userdef, diction, firsts
	# recursion base condition
	# (for terminal or epsilon)
	if len(rule) != 0 and (rule is not None):
		if rule[0] in term_userdef:
			return rule[0]
		elif rule[0] == '#':
			return '#'

	# condition for Non-Terminals
	if len(rule) != 0:
		if rule[0] in list(diction.keys()):
			# fres temporary list of result
			fres = []
			rhs_rules = diction[rule[0]]
			# call first on each rule of RHS
			# fetched (& take union)
			for itr in rhs_rules:
				indivRes = first(itr)
				if type(indivRes) is list:
					for i in indivRes:
						fres.append(i)
				else:
					fres.append(indivRes)

			# if no epsilon in result
			# - received return fres
			if '#' not in fres:
				return fres
			else:
				# apply epsilon
				# rule => f(ABC)=f(A)-{e} U f(BC)
				newList = []
				fres.remove('#')
				if len(rule) > 1:
					ansNew = first(rule[1:])
					if ansNew != None:
						if type(ansNew) is list:
							newList = fres + ansNew
						else:
							newList = fres + [ansNew]
					else:
						newList = fres
					return newList
				# if result is not already returned
				# - control reaches here
				# lastly if eplison still persists
				# - keep it in result of first
				fres.append('#')
				return fres


# calculation of follow
# use 'rules' list, and 'diction' dict from above

# follow function input is the split result on
# - Non-Terminal whose Follow we want to compute
def follow(nt):
	global start_symbol, rules, nonterm_userdef, \
		term_userdef, diction, firsts, follows
	# for start symbol return $ (recursion base case)

	solset = set()
	if nt == start_symbol:
		# return '$'
		solset.add('$')

	# check all occurrences
	# solset - is result of computed 'follow' so far

	# For input, check in all rules
	for curNT in diction:
		rhs = diction[curNT]
		# go for all productions of NT
		for subrule in rhs:
			if nt in subrule:
				# call for all occurrences on
				# - non-terminal in subrule
				while nt in subrule:
					index_nt = subrule.index(nt)
					subrule = subrule[index_nt + 1:]
					# empty condition - call follow on LHS
					if len(subrule) != 0:
						# compute first if symbols on
						# - RHS of target Non-Terminal exists
						res = first(subrule)
						# if epsilon in result apply rule
						# - (A->aBX)- follow of -
						# - follow(B)=(first(X)-{ep}) U follow(A)
						if '#' in res:
							newList = []
							res.remove('#')
							ansNew = follow(curNT)
							if ansNew != None:
								if type(ansNew) is list:
									newList = res + ansNew
								else:
									newList = res + [ansNew]
							else:
								newList = res
							res = newList
					else:
						# when nothing in RHS, go circular
						# - and take follow of LHS
						# only if (NT in LHS)!=curNT
						if nt != curNT:
							res = follow(curNT)

					# add follow result in set form
					if res is not None:
						if type(res) is list:
							for g in res:
								solset.add(g)
						else:
							solset.add(res)
	return list(solset)


def computeAllFirsts():
	global rules, nonterm_userdef, \
		term_userdef, diction, firsts
	for rule in rules:
		k = rule.split("->")
		# remove un-necessary spaces
		k[0] = k[0].strip()
		k[1] = k[1].strip()
		rhs = k[1]
		multirhs = rhs.split('|')
		# remove un-necessary spaces
		for i in range(len(multirhs)):
			multirhs[i] = multirhs[i].strip()
			multirhs[i] = multirhs[i].split()
		diction[k[0]] = multirhs

	st.subheader('Rules:')
	for y in diction:
		st.text(f"{y}->{diction[y]}")
	st.subheader(f"After elimination of left recursion:")

	diction = removeLeftRecursion(diction)
	for y in diction:
		st.text(f"{y}->{diction[y]}")
	st.subheader("After left factoring:")

	diction = LeftFactoring(diction)
	for y in diction:
		st.text(f"{y}->{diction[y]}")

	# calculate first for each rule
	# - (call first() on all RHS)
	for y in list(diction.keys()):
		t = set()
		for sub in diction.get(y):
			res = first(sub)
			if res != None:
				if type(res) is list:
					for u in res:
						t.add(u)
				else:
					t.add(res)

		# save result in 'firsts' list
		firsts[y] = t

	st.subheader("Calculated firsts: ")
	key_list = list(firsts.keys())
	index = 0
	for gg in firsts:
		st.text(f"first({key_list[index]}) "
			f"=> {firsts.get(gg)}")
		index += 1


def computeAllFollows():
	global start_symbol, rules, nonterm_userdef,\
		term_userdef, diction, firsts, follows
	for NT in diction:
		solset = set()
		sol = follow(NT)
		if sol is not None:
			for g in sol:
				solset.add(g)
		follows[NT] = solset

	st.subheader("Calculated follows: ")
	key_list = list(follows.keys())
	index = 0
	for gg in follows:
		st.text(f"follow({key_list[index]})"
			f" => {follows[gg]}")
		index += 1


# create parse table
def createParseTable():
	import copy
	global diction, firsts, follows, term_userdef
	st.subheader("Firsts and Follow Result table")

	# find space size
	mx_len_first = 0
	mx_len_fol = 0
	for u in diction:
		k1 = len(str(firsts[u]))
		k2 = len(str(follows[u]))
		if k1 > mx_len_first:
			mx_len_first = k1
		if k2 > mx_len_fol:
			mx_len_fol = k2

	st.text(f"{{:<{15}}} "
		f"{{:<{mx_len_first + 5}}} "
		f"{{:<{mx_len_fol + 5}}}"
		.format("Non-T", "FIRST", "FOLLOW"))
	for u in diction:
		st.text(f"{{:<{15}}} "
			f"{{:<{mx_len_first + 5}}} "
			f"{{:<{mx_len_fol + 5}}}"
			.format(u, str(firsts[u]), str(follows[u])))

	# create matrix of row(NT) x [col(T) + 1($)]
	# create list of non-terminals
	ntlist = list(diction.keys())
	terminals = copy.deepcopy(term_userdef)
	terminals.append('$')

	# create the initial empty state of ,matrix
	mat = []
	for x in diction:
		row = []
		for y in terminals:
			row.append('')
		# of $ append one more col
		mat.append(row)

	# Classifying grammar as LL(1) or not LL(1)
	grammar_is_LL = True

	# rules implementation
	for lhs in diction:
		rhs = diction[lhs]
		for y in rhs:
			res = first(y)
			# epsilon is present,
			# - take union with follow
			if '#' in res:
				if type(res) == str:
					firstFollow = []
					fol_op = follows[lhs]
					if fol_op is str:
						firstFollow.append(fol_op)
					else:
						for u in fol_op:
							firstFollow.append(u)
					res = firstFollow
				else:
					res.remove('#')
					res = list(res) +\
						list(follows[lhs])
			# add rules to table
			ttemp = []
			if type(res) is str:
				ttemp.append(res)
				res = copy.deepcopy(ttemp)
			for c in res:
				xnt = ntlist.index(lhs)
				yt = terminals.index(c)
				if mat[xnt][yt] == '':
					mat[xnt][yt] = mat[xnt][yt] \
								+ f"{lhs}->{' '.join(y)}"
				else:
					# if rule already present
					if f"{lhs}->{y}" in mat[xnt][yt]:
						continue
					else:
						grammar_is_LL = False
						mat[xnt][yt] = mat[xnt][yt] \
									+ f",{lhs}->{' '.join(y)}"

	st.subheader("\nGenerated parsing table:\n")
	frmt = "‎‎‎{:>12}" * len(terminals)
	st.text(frmt.format(*terminals))

	j = 0
	for y in mat:
		frmt1 = "{:>12}" * len(y)
		st.text(f"{ntlist[j]} {frmt1.format(*y)}")
		j += 1

	return (mat, grammar_is_LL, terminals)


st.title("Parser Table Generator")


rules = st.text_area('Enter Rules', "",help="For ε use # symbol")
rules = rules.split("\n")

nonterm_userdef = st.text_area('Enter Non-terminals', "")
nonterm_userdef = nonterm_userdef.split("\n")

term_userdef = st.text_area('Enter Terminals', "")
term_userdef = term_userdef.split("\n")

if st.button('Generate'):
    st.markdown("""<hr style="height:2px;border:none;color:#333;background-color:#333;" /> """, unsafe_allow_html=True)
    # diction - store rules inputed
    # firsts - store computed firsts
    diction = {}
    firsts = {}
    follows = {}

    # computes all FIRSTs for all non terminals
    computeAllFirsts()
    # assuming first rule has start_symbol
    # start symbol can be modified in below line of code
    start_symbol = list(diction.keys())[0]
    # computes all FOLLOWs for all occurrences
    computeAllFollows()
    # generate formatted first and follow table
    # then generate parse table

    (parsing_table, result, tabTerm) = createParseTable()
