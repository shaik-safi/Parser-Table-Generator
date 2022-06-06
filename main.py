import streamlit as st
import streamlit.components.v1 as components

def removeLeftRecursion(rulesDiction):
	store = {}
	for lhs in rulesDiction:
		alphaRules = []
		betaRules = []
		allrhs = rulesDiction[lhs]
		for subrhs in allrhs:
			if subrhs[0] == lhs:
				alphaRules.append(subrhs[1:])
			else:
				betaRules.append(subrhs)
		if len(alphaRules) != 0:
			lhs_ = lhs + "'"
			while (lhs_ in rulesDiction.keys()) \
					or (lhs_ in store.keys()):
				lhs_ += "'"
			for b in range(0, len(betaRules)):
				betaRules[b].append(lhs_)
			rulesDiction[lhs] = betaRules
			for a in range(0, len(alphaRules)):
				alphaRules[a].append(lhs_)
			alphaRules.append(['#'])
			store[lhs_] = alphaRules
	for left in store:
		rulesDiction[left] = store[left]
	return rulesDiction


def LeftFactoring(rulesDiction):
	newDict = {}
	for lhs in rulesDiction:
		allrhs = rulesDiction[lhs]
		temp = dict()
		for subrhs in allrhs:
			if subrhs[0] not in list(temp.keys()):
				temp[subrhs[0]] = [subrhs]
			else:
				temp[subrhs[0]].append(subrhs)
		new_rule = []
		tempo_dict = {}
		for term_key in temp:
			allStartingWithTermKey = temp[term_key]
			if len(allStartingWithTermKey) > 1:
				lhs_ = lhs + "'"
				while (lhs_ in rulesDiction.keys()) \
						or (lhs_ in tempo_dict.keys()):
					lhs_ += "'"
				new_rule.append([term_key, lhs_])
				ex_rules = []
				for g in temp[term_key]:
					ex_rules.append(g[1:])
				tempo_dict[lhs_] = ex_rules
			else:
				new_rule.append(allStartingWithTermKey[0])
		newDict[lhs] = new_rule
		for key in tempo_dict:
			newDict[key] = tempo_dict[key]
	return newDict

# calculation of first
def first(rule):
	global rules, nonterm_userdef, \
		term_userdef, diction, firsts
	if len(rule) != 0 and (rule is not None):
		if rule[0] in term_userdef:
			return rule[0]
		elif rule[0] == '#':
			return '#'

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

			if '#' not in fres:
				return fres
			else:
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
				fres.append('#')
				return fres


# calculation of follow
def follow(nt):
	global start_symbol, rules, nonterm_userdef, \
		term_userdef, diction, firsts, follows
	solset = set()
	if nt == start_symbol:
		solset.add('$')
	for curNT in diction:
		rhs = diction[curNT]
		for subrule in rhs:
			if nt in subrule:
				while nt in subrule:
					index_nt = subrule.index(nt)
					subrule = subrule[index_nt + 1:]
					if len(subrule) != 0:
						res = first(subrule)
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
						if nt != curNT:
							res = follow(curNT)

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
		k[0] = k[0].strip()
		k[1] = k[1].strip()
		rhs = k[1]
		multirhs = rhs.split('|')
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

	ntlist = list(diction.keys())
	terminals = copy.deepcopy(term_userdef)
	terminals.append('$')

	mat = []
	for x in diction:
		row = []
		for y in terminals:
			row.append('')
		mat.append(row)

	grammar_is_LL = True

	for lhs in diction:
		rhs = diction[lhs]
		for y in rhs:
			res = first(y)
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

#Driver Code
st.title("Parser Table Generator")


rules = st.text_area('Enter Rules', "",help="For ε use # symbol")
rules = rules.split("\n")

nonterm_userdef = st.text_area('Enter Non-terminals', "")
nonterm_userdef = nonterm_userdef.split("\n")

term_userdef = st.text_area('Enter Terminals', "")
term_userdef = term_userdef.split("\n")

if st.button('Generate'):
    st.markdown("""<hr style="height:2px;border:none;color:#333;background-color:#333;" /> """, unsafe_allow_html=True)
    diction = {}
    firsts = {}
    follows = {}

    # computes all FIRSTs for all non terminals
    computeAllFirsts()
    start_symbol = list(diction.keys())[0]
    # computes all FOLLOWs for all occurrences
    computeAllFollows()
    # then generate parse table
    (parsing_table, result, tabTerm) = createParseTable()
