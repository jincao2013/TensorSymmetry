(* ::Package:: *)

(* ::Package:: *)
(**)


BeginPackage["TensorSymmetry`"]

(*
Author: Jin Cao
Email: caojin.phy@gmail.com
version: 0.4
*)


(* Public symbols with usage messages *)
getMPGEnforcedTensor::usage =
  "getMPGEnforcedTensor[rotspec, chi, MPG, internalSymm, naxial, nTR] \
returns {chisym, condition} after applying the tensor symmetry constraints.";
getSSGEnforcedTensor::usage =
  "getSSGEnforcedTensor[rotspec, chi, SSG, internalSymm, nRaxial, nTR] \
returns {chisym, condition} after applying the tensor symmetry constraints.";


(* Define operations *)
spin;
orbi;
soc;
id=RotationMatrix[0,{1,0,0}];
inv=-1*id;
C2x=RotationMatrix[\[Pi],{1,0,0}];
C2y=RotationMatrix[\[Pi],{0,1,0}];
C2z=RotationMatrix[\[Pi],{0,0,1}];
C2xy=RotationMatrix[\[Pi],{1,1,0}];
C3z=RotationMatrix[2\[Pi]/3,{0,0,1}];
C4z=RotationMatrix[\[Pi]/2,{0,0,1}];
C6z=RotationMatrix[\[Pi]/3,{0,0,1}];
C32z=RotationMatrix[\[Pi]/16,{0,0,1}];
Mx=-1*C2x;
My=-1*C2y;
Mz=-1*C2z;
S4z=Mz . C4z;
S6z=Mz . C6z;

(* Define SSG *)
nSSGNoncoplanar={{1,id,id}};
nSSGCoplanar={{-1,C2z,id}};
nSSGColinear={{-1,C2x,id},{1,C32z,id}};

(* Define tensor *)
chiRank1=Table[Subscript[\[Chi], i],{i,{"x","y","z"}}];
chiRank2=Table[Subscript[\[Chi], i<>j],{i,{"x","y","z"}},{j,{"x","y","z"}}];
chiRank3=Table[Subscript[\[Chi], i<>j<>k],{i,{"x","y","z"}},{j,{"x","y","z"}},{k,{"x","y","z"}}];
chiRank4=Table[Subscript[\[Chi], a<>b<>c<>d],{a,{"x","y","z"}},{b,{"x","y","z"}},{c,{"x","y","z"}},{d,{"x","y","z"}}];
IasymabRank3=Table[-Subscript[\[Chi], j<>i<>k],{i,{"x","y","z"}},{j,{"x","y","z"}},{k,{"x","y","z"}}];
IsymbcRank3=Table[-Subscript[\[Chi], j<>i<>k],{i,{"x","y","z"}},{j,{"x","y","z"}},{k,{"x","y","z"}}];

(* Define tensor path *)
(*pathRank2={{2,5},{4,6}};
pathRank3={{2,7},{4,8},{6,9}};
pathRank4={{2,9},{4,10},{6,11},{8,12}};
pathRank5={{2,11},{4,12},{6,13},{8,14},{10,15}};*)

(*DefaultChi::usage =
  "DefaultChi is the default chi tensor used in calculations.";

SymmetryOps::usage =
  "SymmetryOps is the list of default symmetry operations.";
*)



Begin["`Private`"]


getPath[n_]:=Table[{2 k,2 n+k},{k,1,n}];

printTensor[chi_,chisym_,condition_,rank_]:=Switch[rank,
1,(Print[chi];Print[chisym];Print["condition is: ",condition]),
2,(Print[MatrixForm[chi]];Print[MatrixForm[chisym]];Print["condition is: ",condition]),
3,(Print["\!\(\*SubscriptBox[\(\[Chi]\), \(w/o\\\ symm\)]\)  = ",Table[chi[[i]]//MatrixForm,{i,3}]];
Print["\!\(\*SubscriptBox[\(\[Chi]\), \(with\\\ symm\)]\) = ",Table[chisym[[i]]//MatrixForm,{i,3}]];
Print["condition is: ",condition]),
4,(Print["\!\(\*SubscriptBox[\(\[Chi]\), \(w/o\\\ symm\)]\)  = ",Table[chi[[a,b]]//MatrixForm,{a,3},{b,3}]];
Print["\!\(\*SubscriptBox[\(\[Chi]\), \(with\\\ symm\)]\) = ",Table[chisym[[a,b]]//MatrixForm,{a,3},{b,3}]];
Print["condition is: ",condition]),
_,Print["Unsupported rank: ",rank]
];


(* Enforced by MPG *)
getMPGEnforcedRank2Tensor[chi_,ops_,intrinsic_,naxial_,nTR_]:=Module[{chiGroup,condition,chirot,chisym,op,rot,TR},

chiGroup={chi};
chiGroup=chiGroup~Join~intrinsic;

Do[{rot,TR}=op;
chirot=FullSimplify[(TR)^nTR*Det[rot]^naxial*TensorContract[TensorProduct[rot,rot,chi],{{2,5},{4,6}}]];
chiGroup=chiGroup~Join~{chirot},
{op,ops}];

condition=Solve[And@@Equal@@@Partition[chiGroup,2,1]][[1]];

chisym=chi/.condition;
Print["\!\(\*SubscriptBox[\(\[Chi]\), \(w/o\\\ symm\)]\)  = ",chi//MatrixForm];
Print["\!\(\*SubscriptBox[\(\[Chi]\), \(with\\\ symm\)]\) = ",chisym//MatrixForm];
Print["condition is: ",condition];
{chisym,condition}
];

getMPGEnforcedRank3Tensor[chi_,ops_,intrinsic_,naxial_,nTR_]:=Module[{chiGroup,condition,chirot,chisym,op,rot,TR},
(*chi=Table[Subscript[\[Chi], i<>j<>k],{i,{"x","y","z"}},{j,{"x","y","z"}},{k,{"x","y","z"}}];*)

chiGroup={chi};
chiGroup=chiGroup~Join~intrinsic;

Do[{rot,TR}=op;
chirot=FullSimplify[(TR)^nTR*Det[rot]^naxial*TensorContract[TensorProduct[rot,rot,rot,chi],{{2,7},{4,8},{6,9}}]];
chiGroup=chiGroup~Join~{chirot},
{op,ops}];

condition=Solve[And@@Equal@@@Partition[chiGroup,2,1]][[1]];

chisym=chi/.condition;
Print["\!\(\*SubscriptBox[\(\[Chi]\), \(w/o\\\ symm\)]\)  = ",Table[chi[[i]]//MatrixForm,{i,3}]];
Print["\!\(\*SubscriptBox[\(\[Chi]\), \(with\\\ symm\)]\) = ",Table[chisym[[i]]//MatrixForm,{i,3}]];
Print["condition is: ",condition];
{chisym,condition}
];

getMPGEnforcedRank4Tensor[chi_,ops_,intrinsic_,naxial_,nTR_]:=Module[{chiGroup,condition,chirot,chisym,op,rot,TR},

chiGroup={chi};
chiGroup=chiGroup~Join~intrinsic;

Do[{rot,TR}=op;
chirot=FullSimplify[(TR)^nTR*Det[rot]^naxial*TensorContract[TensorProduct[rot,rot,rot,rot,chi],{{2,9},{4,10},{6,11},{8,12}}]];
chiGroup=chiGroup~Join~{chirot},
{op,ops}];

condition=Solve[And@@Equal@@@Partition[chiGroup,2,1]][[1]];

chisym=chi/.condition;
Print["\!\(\*SubscriptBox[\(\[Chi]\), \(w/o\\\ symm\)]\)  = ",Table[chi[[a,b]]//MatrixForm,{a,3},{b,3}]];
Print["\!\(\*SubscriptBox[\(\[Chi]\), \(with\\\ symm\)]\) = ",Table[chisym[[a,b]]//MatrixForm,{a,3},{b,3}]];
Print["condition is: ",condition];
{chisym,condition}
];

getMPGEnforcedRank5Tensor[chi_,ops_,intrinsic_,naxial_,nTR_]:=Module[{chiGroup,condition,chirot,chisym,op,rot,TR},
chiGroup={chi};
chiGroup=chiGroup~Join~intrinsic;

Do[{rot,TR}=op;
chirot=FullSimplify[(TR)^nTR*Det[rot]^naxial*TensorContract[TensorProduct[rot,rot,rot,rot,rot,chi],{{2,11},{4,12},{6,13},{8,14},{10,15}}]];
chiGroup=chiGroup~Join~{chirot},
{op,ops}];

condition=Solve[And@@Equal@@@Partition[chiGroup,2,1]][[1]];

chisym=chi/.condition;
{chisym,condition}
];


(* Enforced by Magnetic point group *)
getMPGEnforcedTensor[rotspec_,chi_,ops_,internalSymm_,naxial_,nTR_]:=Module[{chiGroup,path,condition,chirot,chisym,op,rot,TR},

chiGroup={chi};
chiGroup=chiGroup~Join~internalSymm;

path=getPath[Length[rotspec]];
Do[{TR,rot}=op;
chirot=FullSimplify[(TR)^nTR*Det[rot]^naxial*TensorContract[TensorProduct@@Append[rotspec/.{"rot"->rot},chi],Evaluate[path]]];
chiGroup=chiGroup~Join~{chirot},
{op,ops}];

condition=Solve[And@@Equal@@@Partition[chiGroup,2,1]][[1]];

chisym=chi/.condition;
printTensor[chi,chisym,condition,Length[rotspec]];
{chisym,condition}
];


(* Enforced by Spin point group *)
getSSGEnforcedTensor[rotspec_,chi_,ops_,internalSymm_,nRaxial_,nTR_]:=Module[{chiGroup,path,condition,chirot,chisym,op,TR,rotU,rotR},

chiGroup={chi};
chiGroup=chiGroup~Join~internalSymm;

path=getPath[Length[rotspec]];
Do[{TR,rotU,rotR}=op;
rotU=rotU*Det[rotU];
chirot=FullSimplify[(TR)^nTR*Det[rotR]^nRaxial*TensorContract[TensorProduct@@Append[rotspec/.{"rotU"->rotU,"rotR"->rotR},chi],Evaluate[path]]];
chiGroup=chiGroup~Join~{chirot},
{op,ops}];

condition=Solve[And@@Equal@@@Partition[chiGroup,2,1]][[1]];

chisym=chi/.condition;
printTensor[chi,chisym,condition,Length[rotspec]];
{chisym,condition}
];


End[]

EndPackage[]

