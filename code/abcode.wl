(* ::Package:: *)

(* basic fun *)
capexpand = {ab[x___, cap[{a_, b_}, {c__}], y___] :> ab[b, c] ab[x, a, y] + ab[c, a] ab[x, b, y]};
cap1expand={ab[a_,cap1[{b_,c_},{d_,e_},{f_,g_}]]:>ab[a,b,d,e]ab[a,c,f,g]-ab[a,b,f,g]ab[a,c,d,e]};
cap2expand=ab[a___,cap2[{c_,d_,e_},{f_,g_,h_}],b___]:>ab[a,c,d,b]ab[e,f,g,h]+ab[a,d,e,b]ab[c,f,g,h]+ab[a,e,c,b]ab[d,f,g,h];
cap3expand=ab[cap3[x_,y_,z_,w_]]:>ab[cap2[x,y],cap2[z,w]];
sixR[a_,b_,c_,d_,e_,f_]:=R[a,b,c,d,f]+R[a,b,c,f,e]+R[a,b,d,e,f]+R[a,c,d,f,e]+R[b,c,d,e,f]
shifexp={ab[x___,shift[y_,z_],w___]:>ab[x,y[[1]],w]+z ab[x,y[[2]],w]};
ordercup[exp_]:=SortBy[exp,Which[Head[#]===cap,1.5,Head[#]===shift,1.4,True,#]&];
sortR={i_R:>ordercup[i]Signature[i]Signature[ordercup[i]]};
sortab={i_ab/;FreeQ[i,cap2]:>ordercup[i]Signature[i]Signature[ordercup[i]]};
sortcap1={ab[a_,cap1[b_,c_,d_]]:>ab[a,cap1@@SortBy[{Sort[b],Sort[c],Sort[d]},First]]Signature[b]Signature[c]Signature[d]Signature[SortBy[{Sort[b],Sort[c],Sort[d]},First]]Signature[{Sort[b],Sort[c],Sort[d]}]};
sortcap3=ab[cap3[x_,y_,z_,w_]]:>((neab1[ab[cap3[x,y,z,w]]/.cap3expand//.cap2expand]/neab1[#/.cap3expand//.cap2expand]#)&@ab[cap3@@(Sort[Sort/@{x,y,z,w}])]);
unsortcap2=ab[z___,cap2[x_,y_],w___]:>ab[Sequence@@Sort[{z,w}],cap2[Sequence@@Sort[{Sort[x],Sort[y]}]]];
unsortcap3=ab[cap3[x_,y_,z_,w_]]:>ab[cap3@@(SortBy[Sort/@{x,y,z,w},First])];
tocaps={-ab[a__]ab[b__]+ab[c__]ab[d__]:>If[FreeQ[{a,b,c,d},cap2|cap1|cap],With[{deg2=Intersection[{a},{b},{c},{d}],hh=Tally/@Transpose@Select[Flatten[Outer[List,{a},{b}],1],!(SubsetQ[{c},#]||SubsetQ[{d},#])&]},If[neab1[(#-(-ab[a]ab[b]+ab[c]ab[d]))/.cap1expand]===0,#,-#]&@If[deg2==={},(ab[cap[{#[[1,1]],#[[3,1]]},#[[2]]],Sequence@@#[[4]]]&@Flatten[{First/@Select[#,Last[#]==1&],First/@Select[#,Last[#]==3&]}&/@hh,1]),If[Length[deg2]===1,ab[First[deg2],cap1[{#[[1,1]],#[[3,1]]},#[[4]],#[[2]]]]&@Flatten[({First/@Select[#,Last[#]==1&],First/@Select[#,Last[#]==2&]}&/@hh),1],twistorSimplify[-ab[a]ab[b]+ab[c]ab[d]]]]],-ab[a]ab[b]+ab[c]ab[d]]};
tocap2={ab[z___,cap[x_,y_],w___]:>((neab[#/.cap2expand]/neab[ab[z,cap[x,y],w]])#&[ab[Sequence@@(Sort[x]),cap2@@(SortBy[{Sort[y],Sort[{z,w}]},First])]])};

Zs=Table[Binomial[n+i,i],{n,20},{i,0,3}];
randomPositiveZs[n_]:=(Zs=Nest[Function[{mat},Block[{hatted=Append[(Append[Total[mat[[#1;;-1]]],1]&)/@Range[2,Length[mat]],Append[PadRight[{},Length[mat[[1]]]],1]],newRow=RandomInteger[{1,10},{Length[mat]}]},newRow hatted]],RandomInteger[{1,10},{n+8,1}],3];Zs=Transpose[Inverse[Transpose[Zs[[{1,2,3,4}]]]] . Transpose[Zs]][[5;;-1]];)
neabp[exp_]:=exp/. shifexp//. capexpand//.cap1expand//.cap2expand//.cap3expand/. ab[x__]:>Det[Zs[[{x}]]];
ab[___,j_,___,j_,___]:=0;
sortdoubleab={i_doubleab:>Sort[i]Signature[i]/Signature[Sort[i]]};
shifexp={ab[x___,shift[y_,z_],w___]:>ab[x,y[[1]],w]+z ab[x,y[[2]],w]};
mom=RandomInteger[{-100,100},{20,4}];
mom1=Table[Binomial[n+i,i],{n,20},{i,0,3}];
neab[exp_]:=exp/.shifexp//.capexpand//.cap1expand//.cap2expand//.cap3expand/.ab[x__]:>Det[mom[[{x}]]];
neab1[exp_]:=exp/.shifexp//.capexpand/.ab[x__]:>Det[mom1[[{x}]]];
sortcapinR=R[a__]:>R@@(Replace[List[a],cap[x_,y_]:>cap[ordercup@x,ordercup[y]],{0,Infinity}]);
cap1tocap={ab[a_,cap1[{b_,c_},{d_,e_},{f_,g_}]]:>ab[cap[{b,c},{a,f,g}],a,d,e]};

order[exprn_,option_:1]:=If[option==0,exprn/.{ab[x__]:>Signature[{x}] ab@@Sort[{x}]},Block[{nGuess=Max[Join[{0},Flatten[Apply[List,Cases[exprn,_ab,{0,\[Infinity]}],{1}]]]],consec,xLike},consec=Partition[Range[nGuess],2,1,1];xLike=Apply[If[Length[Range[#2,#3]]>Length[Range[#4,#1+nGuess]],{#3,#4,#1,#2},{##1}]&,Select[Flatten/@Subsets[consec,{2}],Length[#1\[Intersection]#1]==4&],{1}];exprn/.{ab[x__]:>If[Length[{x}]==2,(If[Length[#1]==1,Signature[#1[[1]]] Signature[{x}] ab@@#1[[1]],Signature[{x}] ab@@Sort[{x}]]&)[Select[consec,Length[{x}\[Intersection]#1]==2&,1]],(If[Length[#1]==1,Signature[#1[[1]]] Signature[{x}] ab@@#1[[1]],Block[{xLikeLines=Select[consec,Length[#1\[Intersection]{x}]==2&],boundaries},If[Length[xLikeLines]==0,Signature[{x}] ab@@Sort[{x}],boundaries=Complement[{x},xLikeLines[[1]]];If[Length[Range[boundaries[[2]],If[xLikeLines[[1,1]]<boundaries[[2]],nGuess,0]+xLikeLines[[1,1]]]]+Length[Range[xLikeLines[[1,2]],If[boundaries[[1]]<xLikeLines[[1,2]],nGuess,0]+boundaries[[1]]]]>Length[Range[boundaries[[1]],If[xLikeLines[[1,1]]<boundaries[[1]],nGuess,0]+xLikeLines[[1,1]]]]+Length[Range[xLikeLines[[1,2]],If[boundaries[[2]]<xLikeLines[[1,2]],nGuess,0]+boundaries[[2]]]],boundaries=Reverse[boundaries];];-Signature[Join[boundaries,xLikeLines[[1]]]] Signature[{x}] ab@@RotateLeft[Join[boundaries,xLikeLines[[1]]]]]]]&)[Select[xLike,Length[#1\[Intersection]{x}]==4&]]]}]];
twistorSchouten=#1//.{ab[a___,x_,b___,y_,c___] ab[d___,x_,e___,y_,f___]:>Signature[Flatten[{x,y,Sort[{a,b,c}]}]] Signature[{a,x,b,y,c}] Signature[Flatten[{x,y,Sort[{d,e,f}]}]] Signature[{d,x,e,y,f}] ab@@Flatten[{x,y,Sort[{a,b,c}]}] ab@@Flatten[{x,y,Sort[{d,e,f}]}],ab[a___,x_,b___,y_,c___] ab[d___,y_,e___,x_,f___]:>Signature[Flatten[{x,y,Sort[{a,b,c}]}]] Signature[{a,x,b,y,c}] Signature[Flatten[{x,y,Sort[{d,e,f}]}]] Signature[{d,y,e,x,f}] ab@@Flatten[{x,y,Sort[{a,b,c}]}] ab@@Flatten[{x,y,Sort[{d,e,f}]}]}//.{ab[x_,y_,a_,b_] ab[x_,y_,c_,d_]-ab[x_,y_,a_,d_] ab[x_,y_,c_,b_]:>ab[x,y,a,c] ab[x,y,b,d],ab[x_,y_,a_,b_] ab[x_,y_,c_,d_]-ab[x_,y_,a_,c_] ab[x_,y_,b_,d_]:>ab[x,y,a,d] ab[x,y,c,b],ab[x_,y_,a_,b_] ab[x_,y_,c_,d_]+ab[x_,y_,a_,d_] ab[x_,y_,b_,c_]:>ab[x,y,a,c] ab[x,y,b,d],ab[x_,y_,a_,b_] ab[x_,y_,c_,d_]+ab[x_,y_,a_,c_] ab[x_,y_,d_,b_]:>ab[x,y,a,d] ab[x,y,c,b],-ab[x_,y_,a_,b_] ab[x_,y_,c_,d_]-ab[x_,y_,a_,d_] ab[x_,y_,b_,c_]:>-ab[x,y,a,c] ab[x,y,b,d],-ab[x_,y_,a_,b_] ab[x_,y_,c_,d_]-ab[x_,y_,a_,c_] ab[x_,y_,d_,b_]:>-ab[x,y,a,d] ab[x,y,c,b]}&;
twistorSimplify[exprn_,orderQ_:0]:=If[Count[exprn,ab[x_,y_],\[Infinity]]>0,Simplify[order[exprn]/.Apply[Rule,({#1,twistorSchouten[#1]}&)/@Cases[exprn,ab[x__] ab[y__]-ab[z__] ab[w__]|ab[x__] ab[y__]+ab[z__] ab[w__],{0,\[Infinity]}],{1}]],order[FullSimplify[If[orderQ==1,order[FullSimplify[order[exprn,0],TransformationFunctions->{Automatic,twistorSchouten}],1],exprn],TransformationFunctions->{Automatic,twistorSchouten}],1]];

randomPositiveZs[20];

monic[preexp_]:=With[{exp=Together[preexp]},With[{d1=D[Numerator[exp],\[Tau]],d2=D[Denominator[exp],\[Tau]]},Which[d1===0,{1/(\[Tau]+Simplify[(Denominator[exp]/.\[Tau]->0)/d2]/.tocaps/.sortab),Simplify[Numerator[exp]/d2]/.tocaps/.sortab},d2===0,{(\[Tau]+Simplify[(Numerator[exp]/.\[Tau]->0)/d1]/.tocaps/.sortab),Simplify[d1/Denominator[exp]]/.tocaps/.sortab},d1=!=0&&d2=!=0,{(\[Tau]+Simplify[(Numerator[exp]/.\[Tau]->0)/d1]/.tocaps/.sortab)/(\[Tau]+Simplify[(Denominator[exp]/.\[Tau]->0)/d2]/.tocaps/.sortab),Simplify[d1/d2]/.tocaps/.sortab}]]];
logmonic[exp_]:=With[{hh=monic[exp]},Total[log/@hh]];

(* some symbol calculation *)
GetAlphabet[x_]:=Cases[x,Tensor[y__]:>y,Infinity]//Union
(*
tensor[x___,y_ z_,w___]:=tensor[x,y,w]+tensor[x,z,w]
tensor[x___,y_ /z_,w___]:=tensor[x,y,w]-tensor[x,z,w]
*)
tensor[___,1|-1,___]:=0
tensor[x___,1/y_,w___]:=-tensor[x,y,w]
tensor[x___,y_^a_Integer,w___]:=a tensor[x,y,w]
tensor[x___,y_,w___]/;y=!=0&&y===First@Sort[{-y,y}]:=tensor[x,-y,w]
expandTensor[exp_]:=Expand[exp/.Tensor->tensor,_tensor]/.tensor->Tensor
ExpandTensor[exp_]:=expandTensor[exp/.Dispatch[#->Factor[#]&/@GetAlphabet[exp]]/.Tensor[x___]:>Distribute[Tensor[x],Times,Tensor,Plus]]
(*ExpandTensor[exp_]:=expandTensor[exp/.Tensor[x__]:>Tensor@@(Factor/@{x})]*)
Shuffle[s1_,s2_]:=Module[{p,tp,ord},p=Permutations@Join[1&/@s1,0&/@s2]\[Transpose];tp=BitXor[p,1];ord=Accumulate[p] p+(Accumulate[tp]+Length[s1]) tp;Outer[Part,{Join[s1,s2]},ord,1][[1]]\[Transpose]]
isRationalSymbolzero[$x_]:=If[$x===0,True,If[!(Chop[$x/.Tensor[y__]:>N[Times@@(Log/@Abs/@{y}),100]]===0),False,With[{weights=Length/@(Cases[1+$x,_Tensor,Infinity]//Union),x=$x/.Tensor[___,1|-1,___]:>0/.Tensor[y__]:>Tensor@@(Abs/@{y})},If[SameQ@@weights,If[weights[[1]]===1,Chop[N[#,50]&/@(x/.Tensor[x_]:>Log[Abs[x]])]===0,Module[{HH,hh,basis,coeffs},hh=Expand[x/.Tensor[y_,z__]:>Sum[aaa[[2]]HH[aaa[[1]]]Tensor[z],{aaa,FactorInteger[y]}],_Tensor|_HH];basis=Cases[hh,_HH,Infinity]//Union;coeffs=Last@CoefficientArrays[hh,basis];AllTrue[coeffs,isRationalSymbolzero]]]]]]]

sqrtnorm[a_+b_ Sqrt[c_]]:=a^2 - b^2 c
sqrtnorm[a_+ Sqrt[c_]]:=a^2 - c
finv[x_]:=finv[x]=Quiet[Check[FindIntegerNullVector[x,ZeroTest->(Quiet[N[#,500]]==0&)],False],{FindIntegerNullVector::rnfu,FindIntegerNullVector::nlist}]
FINV[x_,y_]:=With[{temp1=finv[Last/@x]},If[BooleanQ[temp1],{x,y},With[{temp2=First@First@Solve[temp1 . (First/@x)==0]},FINV[DeleteCases[x,First[temp2]->_],Append[Simplify/@(y//.temp2),temp2]]]]]
findalgrel[irrletters_]:=Module[{backrule,rule,relations,temp},backrule=Dispatch@Table[irrletters[[i]]->Sqrt[Abs@sqrtnorm[irrletters[[i]]]]Subscript[$a$, i],{i,Length@irrletters}];rule=Table[log[Subscript[$a$, i]]->Log[Abs@irrletters[[i]]/Sqrt[Abs@sqrtnorm[irrletters[[i]]]]],{i,Length@irrletters}];temp=FINV[rule,{}];relations=Dispatch[Last[FINV[rule,{}]]//.{-log[x_]:>log[1/x],log[x_]+log[y_]:>log[x y],log[x_]-log[y_]:>log[x/y],a_Rational log[x_]:>log[x^a],a_Integer log[x_]:>log[x^a]}/.log->Identity];{backrule,relations,First/@First[temp]/.log->Identity}];
preissymbolzero[prenumt_]:=Module[{numt,rels,randomvar},rels=findalgrel@Select[GetAlphabet[prenumt],!Element[#,Rationals]&];numt=prenumt/.rels[[1]]/.rels[[2]];randomvar=#->RandomPrime[10^7]&/@rels[[3]];numt=ExpandTensor[numt/.randomvar]//.Tensor[x___,Power[a_,b_],y___]:>b Tensor[x,a,y];isRationalSymbolzero[numt]]
issymbolzero[prenumt_]:=If[prenumt===0,True,preissymbolzero[ExpandTensor[prenumt]]]

(* old version:
(* integrate symbol, debug mode *)
(* if the integral is finite, all ctensors with 0 will cancel with each other *)
Clear[cint,ctensor]
(*ctensor[___,1|-1,___]:=0*)
ctensor[x___,b_. ctensor[a__]+c_.,y___]:=(If[c===0,b ctensor[x,a,y],b ctensor[x,a,y]+ctensor[x,c,y]])/;IntegerQ[b]
cint[a_+b_,{\[Tau]_,x_,y_}]:=cint[a,{\[Tau],x,y}]+cint[b,{\[Tau],x,y}]
cint[b_cinteger ctensor[c_],{\[Tau]_,x_,y_}]:=b cint[ctensor[c],{\[Tau],x,y}]
cint[ctensor[a__,\[Tau]_+b_.] dlog[\[Tau]_+c_.],{\[Tau]_,x_,y_}]:=If[y===Infinity,0,(ctensor[a,\[Tau]+b,\[Tau]+c]/.{\[Tau]->y})]-(ctensor[a,\[Tau]+b,\[Tau]+c]/.{\[Tau]->x})+ctensor[cint[Expand[ctensor[a] dlog[\[Tau]+c]],{\[Tau],x,y}],b-c]-ctensor[cint[Expand[ctensor[a] dlog[\[Tau]+b]],{\[Tau],x,y}],b-c]
cint[ctensor[a__,b_] dlog[\[Tau]_+c_.],{\[Tau]_,x_,y_}]:=If[y===Infinity,0,(ctensor[a,b,\[Tau]+c]/.{\[Tau]->y})]-(ctensor[a,b,\[Tau]+c]/.{\[Tau]->x})+ctensor[cint[Expand[ctensor[a] dlog[\[Tau]+c]],{\[Tau],x,y}],b]/;FreeQ[b,\[Tau]]
cint[ctensor[\[Tau]_+b_.] dlog[\[Tau]_+c_.],{\[Tau]_,x_,y_}]:=If[y===Infinity,ctensor[b+x,b-c]-ctensor[b+x,c+x]-ctensor[c+x,b-c],ctensor[b+x,b-c]-ctensor[b+x,c+x]-ctensor[c+x,b-c]-ctensor[b+y,b-c]+ctensor[b+y,c+y]+ctensor[c+y,b-c]]
cint[ctensor[b_.] dlog[\[Tau]_+c_.],{\[Tau]_,x_,y_}]:=If[y===Infinity,-ctensor[b,c+x]-ctensor[c+x,b],-ctensor[b,c+x]+ctensor[b,c+y]-ctensor[c+x,b]+ctensor[c+y,b]]/;FreeQ[b,\[Tau]]
*)

(* integrate symbol, debug mode *)
(* if the integral is finite, all ctensors with 0 will cancel with each other *)
Clear[cint,ctensor]
(*ctensor[___,1|-1,___]:=0*)
ctensor[x___,b_. ctensor[a__]+c_.,y___]/;IntegerQ[b]:=(If[c===0,b ctensor[x,a,y],b ctensor[x,a,y]+ctensor[x,c,y]])
cint[a_+b_,{\[Tau]_,x_,y_}]:=cint[a,{\[Tau],x,y}]+cint[b,{\[Tau],x,y}]
cint[c_ a_,{\[Tau]_,x_,y_}]/;FreeQ[c,\[Tau]|_dlog|_ctensor]:=c cint[a,{\[Tau],x,y}]
cint[ctensor[a__,\[Tau]_+b_.] dlog[\[Tau]_+c_.],{\[Tau]_,x_,y_}]/;FreeQ[c,\[Tau]]&&FreeQ[b,\[Tau]]:=If[y===Infinity,0,(ctensor[a,\[Tau]+b,\[Tau]+c]/.{\[Tau]->y})]-(ctensor[a,\[Tau]+b,\[Tau]+c]/.{\[Tau]->x})+ctensor[cint[Expand[ctensor[a] dlog[\[Tau]+c]],{\[Tau],x,y}],b-c]-ctensor[cint[Expand[ctensor[a] dlog[\[Tau]+b]],{\[Tau],x,y}],b-c]
cint[ctensor[a__,b_] dlog[\[Tau]_+c_.],{\[Tau]_,x_,y_}]/;FreeQ[c,\[Tau]]&&FreeQ[b,\[Tau]]:=If[y===Infinity,0,(ctensor[a,b,\[Tau]+c]/.{\[Tau]->y})]-(ctensor[a,b,\[Tau]+c]/.{\[Tau]->x})+ctensor[cint[Expand[ctensor[a] dlog[\[Tau]+c]],{\[Tau],x,y}],b]
cint[ctensor[\[Tau]_+b_.] dlog[\[Tau]_+c_.],{\[Tau]_,x_,y_}]/;FreeQ[c,\[Tau]]&&FreeQ[b,\[Tau]]:=If[y===Infinity,ctensor[b+x,b-c]-ctensor[b+x,c+x]-ctensor[c+x,b-c],ctensor[b+x,b-c]-ctensor[b+x,c+x]-ctensor[c+x,b-c]-ctensor[b+y,b-c]+ctensor[b+y,c+y]+ctensor[c+y,b-c]]
cint[ctensor[b_.] dlog[\[Tau]_+c_.],{\[Tau]_,x_,y_}]/;FreeQ[c,\[Tau]]&&FreeQ[b,\[Tau]]:=If[y===Infinity,-ctensor[b,c+x]-ctensor[c+x,b],-ctensor[b,c+x]+ctensor[b,c+y]-ctensor[c+x,b]+ctensor[c+y,b]]
cint[ctensor[a___,b_ c_]dlog[d_],{\[Tau]_,x_,y_}]:=cint[ctensor[a,b]dlog[d],{\[Tau],x,y}]+cint[ctensor[a,c]dlog[d],{\[Tau],x,y}]
cint[ctensor[a___,Power[b_,k_]]dlog[d_],{\[Tau]_,x_,y_}]:=Expand[k cint[ctensor[a,b]dlog[d],{\[Tau],x,y}],_ctensor]
cint[ctensor[a___,b_./c_]dlog[d_],{\[Tau]_,x_,y_}]:=cint[ctensor[a,b]dlog[d],{\[Tau],x,y}]-cint[ctensor[a,c]dlog[d],{\[Tau],x,y}]
cint[ctensor[a___]dlog[c_],{\[Tau]_,x_,y_}]/;FreeQ[c,\[Tau]]:=0
cint[ctensor[a___]dlog[c_ d_],{\[Tau]_,x_,y_}]:=cint[ctensor[a]dlog[c],{\[Tau],x,y}]+cint[ctensor[a]dlog[d],{\[Tau],x,y}]
cint[ctensor[a___]dlog[c_./d_],{\[Tau]_,x_,y_}]:=cint[ctensor[a]dlog[c],{\[Tau],x,y}]-cint[ctensor[a]dlog[d],{\[Tau],x,y}]
cint[ctensor[a___]dlog[d_],{\[Tau]_,x_,y_}]/;PolynomialQ[d,\[Tau]]&&Exponent[d,\[Tau]]===1&&D[d,\[Tau]]=!=1:=With[{coeffs=CoefficientList[d,\[Tau]]},cint[ctensor[a]dlog[\[Tau]+Divide@@coeffs],{\[Tau],x,y}]]
cint[ctensor[a___,b_]dlog[d_],{\[Tau]_,x_,y_}]/;PolynomialQ[b,\[Tau]]&&Exponent[b,\[Tau]]===1&&D[b,\[Tau]]=!=1:=With[{coeffs=CoefficientList[b,\[Tau]]},cint[ctensor[a,\[Tau]+Divide@@coeffs]dlog[d],{\[Tau],x,y}]+cint[ctensor[a,Last[coeffs]]dlog[d],{\[Tau],x,y}]]

Clear[newcint,barecint,ctensor]
(*ctensor[___,1|-1,___]:=0*)
ctensor[x___,b_. ctensor[a__]+c_.,y___]/;IntegerQ[b]:=(If[c===0,b ctensor[x,a,y],b ctensor[x,a,y]+ctensor[x,c,y]])
newcint[a_+b_,\[Tau]_/;Head[\[Tau]]=!=List]:=newcint[a,\[Tau]]+newcint[b,\[Tau]]
newcint[c_ a_,\[Tau]_/;Head[\[Tau]]=!=List]/;FreeQ[c,\[Tau]|_dlog|_ctensor]:=c newcint[a,\[Tau]]
newcint[ctensor[a___]dlog[b_],\[Tau]_/;Head[\[Tau]]=!=List]:=(ctensor[a,b]+barecint[ctensor[a]dlog[b],\[Tau]])/.ctensor[___,1|-1,___]:>0
barecint[ctensor[a__,\[Tau]_+b_.] dlog[\[Tau]_+c_.],\[Tau]_]/;FreeQ[c,\[Tau]]&&FreeQ[b,\[Tau]]:=With[{hh=newcint[ctensor[a] dlog[(\[Tau]+c)/(\[Tau]+b)],\[Tau]]},If[hh===0,0,ctensor[newcint[ctensor[a] dlog[(\[Tau]+c)/(\[Tau]+b)],\[Tau]],b-c]]]
barecint[ctensor[a__,b_] dlog[\[Tau]_+c_.],\[Tau]_]/;FreeQ[c,\[Tau]]&&FreeQ[b,\[Tau]]:=ctensor[newcint[ctensor[a] dlog[\[Tau]+c],\[Tau]],b]
barecint[ctensor[\[Tau]_+b_.] dlog[\[Tau]_+c_.],\[Tau]_]/;FreeQ[c,\[Tau]]&&FreeQ[b,\[Tau]]:=ctensor[(c+\[Tau])/(b+\[Tau]),b-c]
barecint[ctensor[b_.] dlog[\[Tau]_+c_.],\[Tau]_]/;FreeQ[c,\[Tau]]&&FreeQ[b,\[Tau]]:= ctensor[b,c+\[Tau]]+ctensor[c+\[Tau],b]
barecint[ctensor[a___,b_ c_] dlog[d_],\[Tau]_]:=barecint[ctensor[a,b] dlog[d],\[Tau]]+barecint[ctensor[a,c] dlog[d],\[Tau]]
barecint[ctensor[a___,b_./c_] dlog[d_],\[Tau]_]:=barecint[ctensor[a,b] dlog[d],\[Tau]]-barecint[ctensor[a,c] dlog[d],\[Tau]]
barecint[ctensor[a___] dlog[c_],\[Tau]_]/;FreeQ[c,\[Tau]]:=0
barecint[ctensor[a___] dlog[c_ d_],\[Tau]_]:=barecint[ctensor[a] dlog[c],\[Tau]]+barecint[ctensor[a] dlog[d],\[Tau]]
barecint[ctensor[a___] dlog[c_./d_],\[Tau]_]:=barecint[ctensor[a] dlog[c],\[Tau]]-barecint[ctensor[a] dlog[d],\[Tau]]
barecint[ctensor[a___] dlog[d_],\[Tau]_]/;PolynomialQ[d,\[Tau]]&&Exponent[d,\[Tau]]===1&&D[d,\[Tau]]=!=1:=With[{coeffs=CoefficientList[d,\[Tau]]},barecint[ctensor[a] dlog[\[Tau]+Divide@@coeffs],\[Tau]]]
barecint[ctensor[a___,b_] dlog[d_],\[Tau]_]/;PolynomialQ[b,\[Tau]]&&Exponent[b,\[Tau]]===1&&D[b,\[Tau]]=!=1:=With[{coeffs=CoefficientList[b,\[Tau]]},barecint[ctensor[a,\[Tau]+Divide@@coeffs] dlog[d],\[Tau]]+barecint[ctensor[a,Last[coeffs]] dlog[d],\[Tau]]]