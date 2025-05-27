(* ***********************************************************
Syntax of DLp

Guides: 
1. Programs and formulas should be taken as parameters, allowing any DIY types; so we introduce two types of programs and formulas as P and F respectively. 
2. We will adopt the approach of ``deep embedding'' of the logic, i.e., we will represent the syntax of the logic as a data type in Coq. 
3. However, we will directly define the proof system of DLp, without showing its correspondence to the semantics of the logic. In other words, our current version will mainly focus on implementing a predicate transformer for the logic. 

************************************************************** *)

Require Import Stdlib.Lists.List.
Import ListNotations. 
Require Import Coq.Bool.Bool.

(* ################## Parameters of DLp ################## *)

Parameter P : Type. (* type of programs *)
Parameter F : Type. (* type of formulas *)
Parameter L : Type. (* type of labels *)

(* PS: temporally, we do not need label mappings, as it only relates to the level of semantics *)

(* assume an equivalence between two atomic formulas in F *)
Parameter eq_F : F -> F -> bool.
(* assume an equivalence between two programs in P *)
Parameter eq_P : P -> P -> bool.
(* assume an equivalence between two labels in L *)
Parameter eq_L : L -> L -> bool.


Section DLpLogic.
(* ################## Syntax of DLp formulas ################## *)

Inductive DLF : Type :=
| tv : DLF (* true *)
| af : F -> DLF (* atomic formula *)
| bx : P -> DLF -> DLF (* box operator *)
| ng : DLF -> DLF (* negation operator *)
| ad : DLF -> DLF -> DLF (* conjunction operator *)
.

Check DLF.

(* additional logical operators *)
(* additional operators are expressed by primitive operators *)

Variable p q : DLF.
Variable a : P.

Definition fv := ng tv. (* false *)

Definition or p q := 
    ng (ad (ng p) (ng q)). (* disjunction operator *)

Definition im p q := 
    or (ng p) q. (* implication operator *)

Definition dm a p := 
    ng (bx a (ng p)). (* diamond operator *) 


Section testFormulas.
    Variable f1 : F.

    Check ng (af f1).
    Compute im (ng (af f1)) (af f1).
    Check or (bx a (af f1)) (bx a (af f1)).
    Compute or (bx a (af f1)) (bx a (af f1)).
    Check dm a (af f1).
    Compute dm a (af f1).
End testFormulas.


(* is dynamic *)
(* we need to check whether a DLp formula is dynamic or not *)
Fixpoint isDymc (p : DLF) : bool :=
    match p with
    | tv => false
    | af f => false
    | bx a p1 => true
    | ng p1 => isDymc p1
    | ad p1 p2 => isDymc p1 || isDymc p2
    end
.

(* is all dynamic *)
Fixpoint isAllDymc (l : list DLF) : bool :=
    match l with
    | [] => true
    | p :: ps => if isDymc p then isAllDymc ps else false
    end
.

(* is all non-dynamic *)
Fixpoint isAllNonDymc (l : list DLF) : bool :=
    match l with
    | [] => true
    | p :: ps => if negb (isDymc p) then isAllNonDymc ps else false
    end
.

Section testIsDynamic.
    Variable f : F.
    Variable a1 : P.
    Variable l : list DLF.

    Compute isDymc (af f).
    Compute isDymc (bx a1 (af f)).
    Compute isDymc (ng (af f)).
    Compute isDymc (ad (af f) (bx a1 (af f))).

    Compute isAllDymc [ ].
    Compute isAllDymc [(af f) ; (ad (af f) (bx a1 (af f)))].
    Compute isAllDymc [(ad (af f) (bx a1 (af f))) ; (bx a1 (af f))].

    Compute isAllNonDymc [ ].
    Compute isAllNonDymc [(af f) ; (ad (af f) (bx a1 (af f)))].
    Compute isAllNonDymc [(af f) ; (ad (af f) (dm a1 (af f)))].
    Compute isAllNonDymc [(ad (af f) (bx a1 (af f))) ; (bx a1 (af f))].
    Compute isAllNonDymc [(ad (af f) (af f)) ; (af f)].

    (* test of negation operator *)
End testIsDynamic.

(* equivalence of DLF formulas *)
Fixpoint eq_DLF (p1 p2 : DLF) : bool :=
    match p1, p2 with
    | tv, tv => true
    | af f1, af f2 => if eq_F f1 f2 then true else false
    | bx a1 p1', bx a2 p2' => if (eq_P a1 a2) && (eq_DLF p1' p2') then true else false
    | ng p1', ng p2' => eq_DLF p1' p2'
    | ad p11 p12, ad p21 p22 => if (eq_DLF p11 p21) && (eq_DLF p12 p22) then true else false
    | _, _ => false
    end
.

End DLpLogic.


(* ***********************************************************
Labelled Sequents of DLp

Guides:
1. DLp's proof system is a labelled one. Labels are one of parameters of DLp, represented as type L. 
2. The basic derivation form is a labelled sequent, which consists of a set of labelled formulas separated by an arrow. 
3. This section consists of the following parts:
    (1) Introductions of labels and label mappings;
    (2) Introduction of basic ingredients of labelled sequents:
        (i) labelled formulas;
        (ii) program transitions (a relation between program states);
        (iii) program terminations.
    (3) Definition of labelled sequents.
4. When designing the structure of sequents and as well as labelled sequents, we need to implement extra structures for cyclic deductions. 
************************************************************** *)


Section DLpSeq.
    (* ################## Labelled formulas ################## *)
    (* program states *)
    Definition PS := prod P L.

    (* labelled formulas *)
    Inductive LDLF : Type :=
    | lb : L -> DLF -> LDLF (* ordinary labelled formula *)
    | pt : PS -> PS -> LDLF (* program transition *)
    | ptr : PS -> LDLF (* program termination *)
    .

    Check LDLF.

    (* equivalence of LDLF formulas *)
    Definition eq_LDLF (p1 p2 : LDLF) : bool :=
        match p1, p2 with
        | lb l1 phi1, lb l2 phi2 => if (eq_L l1 l2) && (eq_DLF phi1 phi2) then true else false
        | pt (a1, l1) (a2, l2), pt (b1, m1) (b2, m2) => 
            if (eq_P a1 b1) && (eq_L l1 m1) && (eq_P a2 b2) && (eq_L l2 m2) then true else false
        | ptr (a, l), ptr (b, m) => if (eq_P a b) && (eq_L l m) then true else false
        | _, _ => false
        end
    .

    (* ################## Labelled sequents ################## *)
    Inductive LSeq : Type :=
    | lseq : (list LDLF) -> (list LDLF) -> LSeq (* labelled sequent *)
    .

    Section testLStruc. (* tests of labelled structures *)
        Variable p : DLF.
        Variable l : L.
        Check lb l p.

        Variable l1 l2 : L.
        Variable a1 a2 : P.
        Check pt (a1, l1) (a2, l2).

        Variable a : P.
        Check ptr (a, l).

        Check lseq.
        Check lseq nil nil.
        Check lseq [ lb l p ; lb l1 p ] [].
    End testLStruc.

    (* ################## Cyclic structures of labelled sequents ################## *)
    (* cyclic information *)
    (* the structure is a pair (\alpha, \pi), where 
        (i) list \alpha is for recording all ancestors of one proof branch;
        (ii) number \pi is for recording the position of nearest progressive step to the current node. *)
    Inductive CycInfo : Type := 
    | cinfo : list LSeq -> nat -> CycInfo 
    .
    
    (* cyclic labelled sequents *)
    Inductive CycLSeq : Type :=
    | cseq : LSeq -> CycInfo -> CycLSeq 
    .

End DLpSeq.


(* ***********************************************************
Other additional functions
************************************************************** *)



(* ***********************************************************
Cyclic Proof System of DLp

Guides:
1. In current version, we directly define the notion of provability of labelled sequents, without showing its correspondence to the semantics of the logic. 
************************************************************** *)

(* program transitions' proof as a parameter *)
Parameter ptprv : CycLSeq -> Prop.

(* program terminations' proof as a parameter *)
Parameter ptrprv : CycLSeq -> Prop.

(* label substitution as a parameter *)
Parameter lsub : L -> L.

(* apply label subsitution on a labeled formula *)
Definition lsubf (sub : L -> L) (p : LDLF) : LDLF :=
    match p with
    | lb l phi => lb (sub l) phi
    | pt (a, l1) (a1, l2) => pt (a, sub l1) (a1, sub l2)
    | ptr (a, l) => ptr (a, sub l)
    end
.

(* apply label substitution to a list of labeled formulas *)
Fixpoint lsubl (sub : L -> L) (l : list LDLF) : list LDLF :=
    match l with
    | [] => []
    | l1 :: ls => (lsubf sub l1) :: (lsubl sub ls)
    end
.

(* assume a match function for labelled sequents *)
Parameter mats : LSeq -> LSeq -> bool.

Section DLpProof.
    (* ################## Cyclic Proof system of DLp ################## *)
    Section testStruc.
        Check lseq.
        Check lb.
        Check cseq.
        Check cinfo.
    End testStruc.


    
    Section testPrv.
    (* DEL
    Inductive prv : CycLSeq -> Prop :=
        alpL : forall (gamma delta : list LDLF) (l : L) (alp : P) (phi : DLF) (R : list LSeq) (pi : nat), 
            let s := (lseq ((lb l (bx alp phi)) :: gamma) delta) in (
                (exists (l2 : L) (alp2 : P), 
                    prv (
                            cseq (lseq gamma ((pt (alp, l) (alp2, l2)) :: delta)) (cinfo nil 0)
                        ) (* side condition *)
                        /\
                            prv (
                                    cseq (lseq ((lb l2 (bx alp2 phi)) :: gamma) delta) (cinfo (s :: R) (pi + 1))
                                )
                )
                        -> (* premise *)
                            prv (
                                    cseq s (cinfo R pi)
                                ) (* conclusion *)
            ) (* end of ``let in'' *)
    .
    *)
    (* 
    Inductive prv : CycLSeq -> Prop :=
    | alpR : forall (gamma delta : list LDLF) (l : L) (alp : P) (phi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq gamma ((lb l (bx alp phi)) :: delta)) in (
            (forall (l' : L) (alp' : P), 
                ptprv (
                        cseq (lseq gamma ((pt (alp, l) (alp', l')) :: delta)) (cinfo nil 0)
                    ) (* side condition *)
                    ->
                    prv (
                            cseq (lseq gamma ((lb l' (bx alp' phi)) :: delta)) (cinfo (s :: R) (pi + 1))
                        ) (* premise *)
            ) (* end of inner forall *)
                -> 
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    .
    *)
    End testPrv. 

    (* manipulation of sequents *)
    (* target a formula in a list of labelled formulas *)
    (* find the formula (to be targeted) in the list, if failed, return the list itself, if success, move this formula to the top of the list, while keeping the remaining of the list as the same as before *)
    Fixpoint tarf_r (p : LDLF) (l : list LDLF) (hd : list LDLF) : list LDLF :=
        match l with
        | nil => hd
        | q :: ls =>
            if (eq_LDLF q p) then
                (q :: hd) ++ ls
            else
                tarf_r p ls (hd ++ [q])
        end
    .

    Definition tarf (p : LDLF) (l : list LDLF) : list LDLF :=
        match l with
        | nil => nil
        | q :: ls => 
            if (eq_LDLF q p) then
                l
            else
                tarf_r p ls [q]
        end
    .

    (* match a sequent in a list of labelled sequents, starting from an index value *)
    Fixpoint matsl (s : LSeq) (l : list LSeq) (i : nat) : bool :=
        match l with
        | nil => false
        | s' :: ls => 
            match i with
            | 0 => if mats s s' then 
                                true 
                            else 
                                matsl s ls 0
            | S i' => matsl s ls i'
            end
        end
    .

    (* provability of labelled sequents *)
    Inductive prv : CycLSeq -> Prop :=
    (* ################## Variations of rules of first-order logic ################## *)
    (* Cut *)
    | cut : forall (gamma delta : list LDLF) (l : L) (phi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq gamma delta) in (
            prv (
                    cseq (lseq gamma ((lb l phi) :: delta)) (cinfo (s :: R) (pi + 1))
                ) (* premise 1 *)
                ->
                    prv (
                            cseq (lseq ((lb l phi) :: gamma) delta) (cinfo (s :: R) (pi + 1))
                        ) (* premise 2 *)
                    ->
                        prv (
                                cseq s (cinfo R pi)
                            ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* Weak R *)
    | wkR : forall (gamma delta : list LDLF) (l : L) (phi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq gamma ((lb l phi) :: delta)) in (
            prv (
                    cseq (lseq gamma delta) (cinfo (s :: R) (pi + 1))
                ) (* premise *)
                ->
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* Weak L *)
    | wkL : forall (gamma delta : list LDLF) (l : L) (phi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq ((lb l phi) :: gamma) delta) in (
            prv (
                    cseq (lseq gamma delta) (cinfo (s :: R) (pi + 1))
                ) (* premise *)
                ->
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* Con R *)
    | conR : forall (gamma delta : list LDLF) (l : L) (phi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq gamma ((lb l phi) :: delta)) in (
            prv (
                    cseq (lseq gamma ((lb l phi) :: (lb l phi) :: delta)) (cinfo (s :: R) (pi + 1))
                ) (* premise *)
                ->
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* Con L *)
    | conL : forall (gamma delta : list LDLF) (l : L) (phi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq ((lb l phi) :: gamma) delta) in (
            prv (
                    cseq (lseq ((lb l phi) :: (lb l phi) :: gamma) delta) (cinfo (s :: R) (pi + 1))
                ) (* premise *)
                ->
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* rule of negation R *)
    | negR : forall (gamma delta : list LDLF) (l : L) (phi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq gamma ((lb l (ng phi)) :: delta)) in (
            prv (
                    cseq (lseq ((lb l phi) :: gamma) delta) (cinfo (s :: R) (pi + 1))
                ) (* premise *)
                ->
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* rule of negation L *)
    | negL : forall (gamma delta : list LDLF) (l : L) (phi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq ((lb l (ng phi)) :: gamma) delta) in (
            prv (
                    cseq (lseq gamma ((lb l phi) :: delta)) (cinfo (s :: R) (pi + 1))
                ) (* premise *)
                ->
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* rule of and R *)
    | andR : forall (gamma delta : list LDLF) (l : L) (phi psi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq gamma ((lb l (ad phi psi)) :: delta)) in (
            prv (
                    cseq (lseq gamma ((lb l phi) :: delta)) (cinfo (s :: R) (pi + 1))
                ) (* premise 1 *)
                ->
                    prv (
                    cseq (lseq gamma ((lb l psi) :: delta)) (cinfo (s :: R) (pi + 1))
                    ) (* premise 2 *)
                    ->
                        prv (
                                cseq s (cinfo R pi)
                            ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* rule of and L *)
    | andL : forall  (gamma delta : list LDLF) (l : L) (phi psi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq ((lb l (ad phi psi)) :: gamma) delta) in (
            prv(
                cseq (lseq ((lb l phi) :: (lb l psi) :: gamma) delta) (cinfo (s :: R) (pi + 1))
            ) (* premise *)
            -> 
                prv(
                    cseq s (cinfo R pi)
                )
        ) (* end of ``let in'' *)
    (* rule of and L for dynamic formulas *)
    (* DEL 
    | andL_d : forall  (gamma delta : list LDLF) (l : L) (phi psi : DLF) (R : list LSeq) (pi : nat), 
        (isAllDymc [phi ; psi] = true) -> (* if both phi and psi are dynamic formulas *)
            let s := (lseq ((lb l (ad phi psi)) :: gamma) delta) in (
                prv(
                    cseq (lseq ((lb l phi) :: gamma) delta) (cinfo (s :: R) (pi + 1))
                ) (* premise *)
                -> 
                    prv(
                        cseq s (cinfo R pi)
                    )
            ) (* end of ``let in'' *)
    *)
    (* ################## Variations of other rules of first-order logic ################## *)
    (* rule of or R *)
    | orR : forall (gamma delta : list LDLF) (l : L) (phi psi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq gamma ((lb l (or phi psi)) :: delta)) in (
            prv (
                    cseq (lseq gamma ((lb l phi) :: (lb l psi) :: delta)) (cinfo (s :: R) (pi + 1))
                ) (* premise *)
                ->
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* rule of or L *)
    | orL : forall (gamma delta : list LDLF) (l : L) (phi psi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq ((lb l (or phi psi)) :: gamma) delta) in (
            prv (
                    cseq (lseq ((lb l phi) :: gamma) delta) (cinfo (s :: R) (pi + 1))
                ) (* premise 1 *)
                ->
                    prv (
                            cseq (lseq ((lb l psi) :: gamma) delta) (cinfo (s :: R) (pi + 1))
                        ) (* premise 2 *)
                    ->
                        prv (
                                cseq s (cinfo R pi)
                            ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* rule of im R *)
    | imR : forall (gamma delta : list LDLF) (l : L) (phi psi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq gamma ((lb l (im phi psi)) :: delta)) in (
            prv (
                    cseq (lseq ((lb l phi) :: gamma) ((lb l psi) :: delta)) (cinfo (s :: R) (pi + 1))
                ) (* premise *)
                ->
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* rule of im L *)
    | imL : forall (gamma delta : list LDLF) (l : L) (phi psi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq ((lb l (im phi psi)) :: gamma) delta) in (
            prv (
                    cseq (lseq gamma ((lb l phi) :: delta)) (cinfo (s :: R) (pi + 1))
                ) (* premise 1 *)
                ->
                    prv (
                            cseq (lseq ((lb l psi) :: gamma) delta) (cinfo (s :: R) (pi + 1))
                        ) (* premise 2 *)
                        ->
                        prv (
                                cseq s (cinfo R pi)
                            ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* ################## Substitution Rule ################## *)
    | sub : forall (gamma delta : list LDLF) (R : list LSeq) (pi : nat), 
        let s := (lseq (lsubl lsub gamma) (lsubl lsub delta)) in (
            prv (
                    cseq (lseq gamma delta) (cinfo (s :: R) (pi + 1))
                ) (* premise *)
                ->
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* ################## Rules for dynamic formulas ################## *)
    (* rule of [alp]R *)
    | alpR : forall (gamma delta : list LDLF) (l : L) (alp : P) (phi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq gamma ((lb l (bx alp phi)) :: delta)) in (
            (forall (l' : L) (alp' : P), 
                ptprv (
                        cseq (lseq gamma ([pt (alp, l) (alp', l')])) (cinfo nil 0)
                    ) (* side condition *)
                    ->
                    prv (
                            cseq (lseq gamma ((lb l' (bx alp' phi)) :: delta)) (cinfo (s :: R) 0) (* [alp]R in our setting is always progressive *)
                        ) (* premise *)
            ) (* end of inner forall *)
                -> 
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* rule of [alp]L *)
    | alpL : forall (gamma delta : list LDLF) (l : L) (alp : P) (phi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq ((lb l (bx alp phi)) :: gamma) delta) in (
            (exists (l' : L) (alp' : P), 
                ptprv (
                        cseq (lseq gamma ([pt (alp, l) (alp', l')])) (cinfo nil 0)
                    ) (* side condition *)
                /\
                prv (
                        cseq (lseq ((lb l' (bx alp' phi)) :: gamma) delta) (cinfo (s :: R) (pi + 1))
                    ) (* premise *)
            ) (* end of exists *)
                -> 
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* rule of [alp]L - progressive *)
    | alpL_p : forall (gamma delta : list LDLF) (l : L) (alp : P) (phi : DLF) (R : list LSeq) (pi : nat), 
        let s := (lseq ((lb l (bx alp phi)) :: gamma) delta) in (
            (exists (l' : L) (alp' : P), 
                ptprv (
                        cseq (lseq gamma ([pt (alp, l) (alp', l')])) (cinfo nil 0)
                    ) (* side condition *)
                /\
                prv (
                        cseq (lseq ((lb l' (bx alp' phi)) :: gamma) delta) (cinfo (s :: R) 0) (* it is progressive *)
                    ) (* premise *)
                /\
                ptrprv (
                            cseq (lseq gamma ([ptr (alp', l')])) (cinfo nil 0)
                        ) (* progressive condition *)
            ) (* end of exists *)
                -> 
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* ################## Rules for manipulating sequents ################## *)
    (* rule of re-target a formula on the left side *)
    | tarfL : forall (gamma delta : list LDLF) (phi : LDLF) (R : list LSeq) (pi : nat), 
        let s := (lseq gamma delta) in (
            prv (
                    cseq (lseq (tarf phi gamma) delta) (cinfo (s :: R) (pi + 1))
                ) (* premise *)
                ->
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* rule of re-target a formula on the right side *)
    | tarfR : forall (gamma delta : list LDLF) (phi : LDLF) (R : list LSeq) (pi : nat), 
        let s := (lseq gamma delta) in (
            prv (
                    cseq (lseq gamma (tarf phi delta)) (cinfo (s :: R) (pi + 1))
                ) (* premise *)
                ->
                    prv (
                            cseq s (cinfo R pi)
                        ) (* conclusion *)
        ) (* end of ``let in'' *)
    (* ################## Rules for cyclic deductions ################## *)
    | cyc : forall (gamma delta : list LDLF) (R : list LSeq) (pi : nat), 
        let s := (lseq gamma delta) in (
            matsl s R pi = true
            -> (* if the sequent s matches with one of the sequents in R starting from position pi *)
                prv (
                        cseq s (cinfo R pi)
                    ) (* conclusion *)
        ) (* end of ``let in'' *)
    .
End DLpProof. 



