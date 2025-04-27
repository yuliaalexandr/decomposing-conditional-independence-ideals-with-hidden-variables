-* 
This code confirms computations in Example 2.9.

This code defines two key functions used in the paper:

1) I(H): Given a hypergraph H, returns the ideal associated with H. 
         This corresponds to the definition of I(H) in the paper.

2) H(S): Given a List S, returns the hypergraph associated with the zero set S. 
         This corresponds to the definition of H(S) in the paper. 
*-

restart

-- fix k, l, d, s, t:
k = 3
l = 5
d = 4

s = 2 -- columns
t = 4 -- rows

-- the matrix Y represents the grid G
Y = reshape(ZZ^k, ZZ^l, matrix{{1..k*l}})

-- the hypergraph Delta
Delta = join( flatten apply(entries Y, i -> subsets(i, t)),
              flatten apply(entries transpose Y, i -> subsets(i, s)) )
	 

R = QQ[splice apply(k*l, i->x_(1, i+1)..x_(d, i+1)), MonomialOrder => Lex]
-- the matrix of indeterminates X
X = reshape(R^d, R^(k*l), matrix{gens R})





-**************************
makes ideal from hypergraph
@param:  List of Lists H
@return: Ideal I(H)
**************************-

I = H -> {
    
-- hashtable to store (k, [d] choose k) pairs
U = unique(apply(H, h -> length h));
subz = new MutableHashTable;
for el in U do subz#el = subsets(1..d, el);

-- get all corresponding minors:
mins = {};
for h in H do {
    c = apply(h, i -> i - 1);
    len = length(h);
    rs = subz#len;
    for el in rs do {r = apply(el, i -> i - 1);
	    	     mins = append(mins, det X_c^r);
	             };
    };

-- make the ideal
return ideal(mins);
}


-- make the ideals I_C and I_Delta:
IDelta = I(Delta);
IEmpty = minors(t, X) + IDelta;








-*****************************
makes hypergraph from zero set
input:  List S
output: List of Lists H(S)
******************************-

H = S -> {
    
HS = {};
M = apply(entries Y, el -> apply(el, i -> if any(S, n -> n==i) then 0 else i));
M = for el in M list if (number(el, i -> i != 0) >= t) then el else continue;

-- make variables
HS = join(HS, apply(S, el -> {el}));

-- make 2-minors
colsY = flatten apply(entries transpose Y, i -> subsets(i, k));
colz = apply(colsY, el -> for i in el list if toList(set({i}) * set(S)) == {} then i else continue);
HS = join(HS, flatten apply(colz, c -> subsets(c, 2)));

-- make (t-1)-minors
for el in subsets(M, 2) do {
    C1 = select(l, i -> (first el)_i != 0);
    C2 = select(l, i -> (last el)_i != 0);
    if length(toList(set C1 - set C2)) < 1 or length(toList(set C2 - set C1)) < 1 then continue
    else {	
	 idx = toList(set C1 * set C2);
	 cols = flatten apply(el, i -> apply(idx, j -> i_j));
         HS = unique join(HS, apply(subsets(cols, t-1), el -> sort(el)));	 
	 }; 
    };

-- make t-minors
rowz = {};
for row in entries Y do {
    for el in S do {
        row = delete(el, row);
	};
rowz = append(rowz, row);};
HS = unique join(HS, flatten apply(rowz, r -> subsets(r, t)));

-- add some missing minors (take closure)
twosubz = select(HS, i -> length(i) == 2);


while(true) do {
nontwosubz =  select(HS, i -> length(i) > 2);


for el1 in nontwosubz do {
    for el2 in twosubz do {
	inters = toList(set(el1) * set(el2));
	if length inters == 1 then {
	  pos = position(el1, i -> i == inters_0);
	  HS = unique( append(HS, sort(replace(pos, (toList(set(el2) - set(inters)))_0, el1))));
	    };
	};
    };

NEWnontwosubz = select(HS, i -> length(i) > 2);
if  NEWnontwosubz == nontwosubz then break;
};

return HS;
}











-- Example 2.9:

S = {6,11,13} 
IS = I(H(S));

for Sb in subsets(S) do {
    ISb = I(H(Sb));
    print(Sb, isSubset(ISb, IS));
    }


dim IS
degree IS

decomp = decompose IS;
length decomp

netList (decomp_0)_*
netList (decomp_1)_*

