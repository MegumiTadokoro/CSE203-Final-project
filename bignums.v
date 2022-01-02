(* --------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Printing Coercions.

(* Doan Dai Nguyen and Pedro Cabral *)

(* --------------------------------------------------------------------- *)
(* The goal of this project is to develop a minimal library for          *)
(* arbitrary-precision arithmetic, also called bignums.                  *)
(*                                                                       *)
(* Arbitrary-precision arithmetic refers to the set of techniques used   *)
(* to manipulate numbers (mainly integers or rational) of arbitrary size *)
(* in a computer program. Arbitraty-precision arithmetic is opposed      *)
(* fixed-precision arithmetic (found in most arithmetic logic unit       *)
(* (ALU) hardware) and that deals only with 32 or 64 bit numbers.        *)
(*                                                                       *)
(* Several modern programming languages have built-in support for        *)
(* bignums (e.g. Python or Coq with the type `nat`), and various         *)
(* libraries provide efficient data structures and operations for        *)
(* arbitrary-precision computing.                                        *)
(*                                                                       *)
(* In most bignum libraries, rather than storing values as a fixed       *)
(* number of bits related to the size of the processor register, they    *)
(* typically use a variable-length arrays of machine words.              *)
(*                                                                       *)
(* For example, on a 32-bit machine, one (unsigned) machine word can     *)
(* store integers from 0 to 2^32 (excluded). If we want to store an      *)
(* integer greater or equal than 2^32, we have to use at least two       *)
(* machine words. For example, if we use exactly two machine words       *)
(* w0 & w1, we have then 64 bits at our disposal and can therefore       *)
(* store integers from 0 to 2^64 (excluded).                             *)
(*                                                                       *)
(* One way to do this is to use a base 2^32 numbering system where `w0`  *)
(* is the units digit and `w1` the tens digit. Thus, the pair of machine *)
(* words `(w0, w1)` represents the number `w0 + 2^32 * w1`.              *)
(*                                                                       *)
(* If we need to store a number larger or equal than `2^64`, we can use  *)
(* a third digit `w2`. In this case, `w2` plays the role of the hundreds *)
(* digit and the triplet (w0, w1, w2) represents the integer             *)
(* `w0 + 2^32 * w1 + 2^(2*32) * w2`. Using three words, we can then      *)
(* represent numbers up to 2^96 (excluded).                              *)
(*                                                                       *)
(* In the case of a bignum library, to represent integers, we use a      *)
(* variable-length array (or list) of machine words. Such a list `ws`    *)
(* represents the integer:                                               *)
(*                                                                       *)
(*    \sum_(0 <= i < |ws|) 2^(i*32) * ws_i                               *)
(*                                                                       *)
(* where `|ws|` is the length of the list `ws` and `ws_i` is the i-th    *)
(* element of `ws`.                                                      *)

(* --------------------------------------------------------------------- *)
(* In this project, to represent bignum, we will use lists of machine    *)
(* words of size `(8 * size)`, where `size` is some positive natural     *)
(* number that represents the size (in bytes) of the hardware            *)
(* machine-word:                                                         *)

Context
  (size     :  nat)
  (gt0_size :  (0 < size)%N)
  (wsize    := 2 ^ (8 * size))
  (word     := 'Z_wsize)
  (bignum   := seq word).

(* -------------------------------------------------------------------- *)
(* We provide some basic results on `wsize`                             *)

Lemma gt1_wsize : 1 < wsize.
Proof.
rewrite /wsize -{1}[1](expn0 2) ltn_exp2l // lt0n.
by rewrite muln_eq0 /= -lt0n gt0_size.
Qed.

Hint Extern 0 (is_true (1 < wsize)) => exact: gt1_wsize : core.

Lemma gt0_wsize : 0 < wsize.
Proof. by apply: (@leq_trans 2). Qed.

Hint Extern 0 (is_true (0 < wsize)) => exact: gt0_wsize : core.

(* Here, 'Z_p is the type of integers modulo `p` that provides a good    *)
(* absraction of what a machine word is. You can use the standard ring   *)
(* operations on values of type 'Z_p.                                    *)

(* Note: the command above is equivalent to:                             *)
(*                                                                       *)
(*   Parameter  (size : nat).                                            *)
(*   Hypothesis (gt0_size : (0 < size)%N)                                *)
(*                                                                       *)
(*   Definition wsize  := 2 ^ (8 * size).                                *)
(*   Definition word   := 'Z_wsize.                                      *)
(*   Definition bignum := seq word.                                      *)

(* --------------------------------------------------------------------- *)
(* In this project, you might want to convert values between natural     *)
(* numbers and words. For that purpose, you can use the `toword` and     *)
(* nat_of_ord operators:                                                 *)

Notation toword n := (inord n : word) (only parsing).

Lemma towordK (n : nat) : n < wsize -> nat_of_ord (toword n) = n.
Proof.
by move=> le; rewrite inordK // !prednK // ltn_predRL.
Qed.

Lemma ofwordK (w : word) : toword (nat_of_ord w) = w.
Proof. by rewrite inord_val. Qed.

Lemma ltn_nat_of_ord (w : word) : nat_of_ord w < wsize.
Proof. by case: w => /= w; rewrite !prednK // ltn_predRL. Qed.

(* --------------------------------------------------------------------- *)
(* In the course of this project, you might want to use the following    *)
(* lemmas about natural integer arithmetic:                              *)
(*                                                                       *)
(*   addn0, add0n, addnC, addnA                                          *)
(*   muln0, mul0n, mulnC, mulnA                                          *)
(*   muln1, mul1n, mulnS                                                 *)
(*                                                                       *)
(* You can do a `Check lemma_name` do this what `lemma_name` proves.     *)
(*                                                                       *)
(* As a general note, if you are stuck because you are missing some      *)
(* basic properties about natural numbers, just put it as an axiom and   *)
(* go forward.                                                           *)


(* ===================================================================== *)
(* Changing the representation (nat <-> bignum)                          *)
(* ===================================================================== *)

(* In this first part, we will write the conversion functions between    *)
(* the natural numbers (the values of type `nat`) and the type           *)
(* `bignum`, as well as proving different results about them. These      *)
(* functions will allow us later to state the correctness lemmas of      *)
(* the implementations of the arithmetic operations.                     *)

(* 1. Implement the function `bn2nat` s.t. `bn2nat z` returns the        *)
(*    natural number represented by the bignum `z`, i.e.                 *)
(*                                                                       *)
(*    bn2nat z := z_0 + z_1 * 2^32 + z_2 * 2^64 + ... + z_n * 2^(n*32)   *)
(*                                                                       *)
(* Values of type 'Z_p are automatically converted to `nat` when needed. *)
(* However, you can force the conversion using the function              *)
(* `nat of ord`.                                                         *)
(*                                                                       *)
(* (In all the question asking you to define a fuction, you are free to  *)
(* change `Definition` to `Fixpoint` if needed).                         *)

Fixpoint bn2nat (z : bignum) : nat :=
  match z with
  | nil => 0
  | z_0::s => (bn2nat s) * wsize + nat_of_ord(z_0)
  end.  

(* 2. Implement the function `nat2bn` s.t. `nat2bn n` computes the       *)
(*    bignum that represents the natural number `n`.                     *)
(*                                                                       *)
(* In this function, you can use the following operations:               *)
(*                                                                       *)
(*   - n %% p : computes `n` modulo `p` for `(n p : nat)`                *)
(*   - n %/ p : computes the quotient of the division of `n` by `p`      *)
(*                                                                       *)

(* In this lemma, you might want to use `divn_eq`                        *)	
(*                                                                       *)	
(*   divn_eq                                                             *)	
(*     : forall m d : nat, m = m %/ d * d + m %% d                       *)	
(*                                                                       *)	
(* We also provide the following lemma:                                  *)	
Lemma nat2bn_help1 n p : n < p.+1 -> n.+1 %/ wsize <= p.
Proof.
move/leq_div2r => /(_ wsize) /leq_trans; apply.
case: p => [|p]; first rewrite divn_small //.
have := leq_divDl wsize p.+1 1; rewrite addn1.
move/leq_trans; apply; rewrite [1%/_]divn_small //.
rewrite addn0 addn1; apply: ltn_Pdiv => //.
Qed.	

Fixpoint nat2bn_aux (depth : nat) (n : nat) : bignum :=
  match depth, n with
  | 0, _ => [::]
  | S d, 0 => [::]
  | S d, S m => [::(inord ((S m) %% wsize)) & (nat2bn_aux d ((S m) %/ wsize))]
  end.

Lemma nat2bn_auxK : forall d n, d >= n -> (bn2nat (nat2bn_aux d n)) = n.
Proof.
elim => [|d] //=.
+ elim => [|n] //=.
+ move => n0 n1.
  case: n1.
  ++ simpl.
     exact.
  ++ move => n H.
     simpl.
     pose proof (nat2bn_help1 H) as H0.
     rewrite towordK.
     +++ move: (n0 (n.+1 %/ wsize) H0) => k.
         rewrite k.
         rewrite -(divn_eq n.+1 wsize).
         exact.
     +++ apply ltn_pmod.
         exact.
Qed. 

(* addn n m == n+m *)

Definition nat2bn (n : nat) : bignum := (nat2bn_aux n n).

(* 3. Prove that `nat2bn` and `bn2nat` are self-invert.                  *)
(*                                                                       *)
(*    Such a result is sufficient to prove that you have a               *)
(*    correct & complete representation of arbitrary-precision           *)
(*    numbers:                                                           *)
(*                                                                       *)
(*      - you can represent any natural number using a bignum, and       *)
(*      - two different bignums never represent the same number.         *)
(*                                                                       *)

Lemma nat2bnK : cancel nat2bn bn2nat.
Proof.
unfold cancel.
intros.
apply nat2bn_auxK.
exact.
Qed.

Definition canon (z : bignum) :=
  if rev z is x :: _ then x != 0%R else true.

Fixpoint canon_alt (z : bignum) :=
  match z with
  | nil => true
  | a :: nil => 
    match val a with  
    | 0 => false
    | S _ => true
    end
  | a :: z' => canon_alt z'
  end.

Lemma bn2natK (z : bignum) :
  canon_alt z -> nat2bn (bn2nat z) = z.
Proof.
induction z.
+ exact.
+ 
Admitted.

(* ===================================================================== *)
(* Addition of bignums                                                   *)
(* ===================================================================== *)

(* We are now interested in adding bignums: given `z1 z2 : bignum`, we   *)
(* want to compute a bignum `bnadd z1 z2` s.t.                           *)
(*                                                                       *)
(*   bn2nat z = bn2nat z1 + b2nat z2                                     *)
(*                                                                       *)
(* Of course, one could directly use the arithmetical operations of      *)
(* `nat` to implement `bn2nat`, i.e.                                     *)
(*                                                                       *)
(*   Definition bn2nat (z1 z2 : bignum) : bignum :=                      *)
(*     bn2nat (nat2bn z1 + nat2bn z2).                                   *)
(*                                                                       *)
(* However, using a bignum library to implement a bignum library would   *)
(* totally defeat the purpose of this project. AS SUCH, IN ALL THIS      *)
(* PROJECT, IT IS STRICTLY FORBIDDEN TO USE THE ARTIHMTIC OF NAT TO      *)
(* IMPLEMENT THE BIGNUM OPERATIONS.                                      *)

(* Instead, we need to come with a way to implement them by only         *)
(* resorting on the machine word arithmetic operations. For addition,    *)
(* the best algorithm is simply the school-book addition that you all    *)
(* learnt in elementary school (here given in pseudo-code):              *)
(*                                                                       *)
(*   proc bnadd(z1 : bignum, z2 : bignum) : bignum {                     *)
(*     n : nat    <- max (size z1, size z2)                              *)
(*     z : bignum <- [::]                                                *)
(*     c : carry  <- false                                               *)
(*                                                                       *)
(*     for i = 0 to n-1 {                                                *)
(*       c, w <- word_add_with_carry(z1_i, z2_i, c)                      *)
(*       z    <- z ++ [:: w]                                             *)
(*     }                                                                 *)
(*     if (c) {                                                          *)
(*       z <- z ++ [:: 1]                                                *)
(*     }                                                                 *)
(*     return z                                                          *)
(*   }                                                                   *)
(*                                                                       *)
(* where `word_add_with_carry(w1, w2, c)` returns a pair `(c2, w)`       *)
(* where `w` is the result of the addition of `w1 + w2 + c` (using       *)
(* modular arithmetic) and `c` is a carry flag (a boolean) that          *)
(* indicates wether an integer overflow occured. Also, to ease the       *)
(* presentation, note that we assumed that `z_i` is the machine word `0` *)
(* when `i` is out of bounds.                                            *)
(*                                                                       *)
(* The operation `word_add_with_carry` is something that is provided by  *)
(* the  ALU of the hardware, and we will assume given its                *)
(* implementation:                                                       *)

Context (word_add_with_carry : word -> word -> bool -> bool * word).

Axiom word_add_with_carry_correct :
  forall (w1 w2 : word) (c : bool),
    let: (c', w) := word_add_with_carry w1 w2 c in
    nat_of_ord w1 + nat_of_ord w2 + nat_of_bool c = w + (nat_of_bool c') * wsize.

(* 4. Implement the function `bnadd` that computes the addition of two   *)
(*    bignums, using the algorithm given above.                          *)

Fixpoint bn_carry (z : bignum) (c : bool) : bignum:=
  match z with
  | nil => [::(toword c)]
  | z_0 :: z_rest =>
    let: (carry, res) := (word_add_with_carry z_0 (toword 0) c) in
      res::(bn_carry z_rest carry)
  end.

Lemma distributivitity (a b c : nat): (a + b)*c = a*c + b*c.
Proof. ring. Qed.

Lemma bn_carry_correct (z : bignum) (c : bool):
  bn2nat (bn_carry z c) = bn2nat z + c.
Proof.
move: c.
induction z.
+ simpl.
  rewrite mul0n.
  intros c.
  case: c; simpl; by rewrite towordK // mul0n // !add0n.
+ simpl.
  intros c.
  case e: (word_add_with_carry a (inord 0) c) => [carry result].
  move: (word_add_with_carry_correct a (inord 0) c).
  rewrite e.
  simpl.
  rewrite towordK // addn0.
  move => eql.
  rewrite IHz.
  rewrite distributivitity.
  apply esym.
  rewrite -addnA.
  rewrite eql.
  rewrite (addnC result (carry*wsize)).
  rewrite addnA.
  exact.
Defined.

Fixpoint bnadd_aux (z1 z2 : bignum) (c : bool) : bignum :=
  match z1, z2 with
  | _, nil => bn_carry z1 c
  | nil, _ => bn_carry z2 c
  | a :: z3, b :: z4 => 
    let: (carry, w) := (word_add_with_carry a b c) in
      w::(bnadd_aux z3 z4 carry)
  end.

Lemma long_associativity_1 (a b c d e : nat):
  a + b + (c + d) + e = b + d + e + a + c.
Proof. ring. Qed.

Lemma long_associativity_2 (a b c d : nat): a + b + c + d = c + d + a + b.
Proof. ring. Qed.

Lemma bnadd_aux_correct (z1 z2 : bignum) (c : bool): 
  bn2nat (bnadd_aux z1 z2 c) = bn2nat z1 + bn2nat z2 + c.
Proof.
move: z2 c.
induction z1.
+ induction z2.
  ++ intros c; case: c; simpl; by rewrite towordK // mul0n // !add0n.
  ++ intros c.
     simpl.
     case e: (word_add_with_carry a (inord 0) c) => [carry result].
     move: (word_add_with_carry_correct a (inord 0) c).
     rewrite e.
     simpl.
     rewrite bn_carry_correct.
     rewrite towordK // addn0.
     move => eql.
     rewrite distributivitity.
     rewrite add0n.
     apply esym.
     rewrite -addnA.
     rewrite eql.
     rewrite (addnC result (carry*wsize)).
     rewrite addnA.
     exact.
+ induction z2.
  ++ intros c.
     simpl.
     case e: (word_add_with_carry a (inord 0) c) => [carry result].
     move: (word_add_with_carry_correct a (inord 0) c).
     rewrite e.
     simpl.
     rewrite bn_carry_correct.
     rewrite towordK.
     rewrite addnACl.
     rewrite add0n.
     rewrite addnC.
     move => eql.
     rewrite distributivitity.
     apply esym.
     rewrite addnACl.
     rewrite add0n.
     rewrite -addnACl.
     rewrite eql.
     rewrite addnCAC.
     exact.
     exact.
  ++ intros c.
     simpl. 
     case e: (word_add_with_carry a a0 c) => [carry result].
     move: (word_add_with_carry_correct a a0 c).
     rewrite e.
     simpl.
     rewrite IHz1.
     move => eql.
     rewrite distributivitity.
     rewrite distributivitity.
     rewrite long_associativity_1.
     rewrite eql.
     rewrite (addnC result (carry*wsize)).
     rewrite long_associativity_2.
     exact.
Qed.

Definition bnadd (z1 z2 : bignum) : bignum := (bnadd_aux z1 z2 false).

(* 5. Prove that `bnadd` is correct, as stated below.                    *)

Lemma bnadd_correct (z1 z2 : bignum): 
  bn2nat (bnadd z1 z2) = bn2nat z1 + bn2nat z2.
Proof. by rewrite bnadd_aux_correct // addn0. Qed.

(* ===================================================================== *)
(* Multiplication of bignums                                             *)
(* ===================================================================== *)

(* We are now interested in adding bignums: given `z1 z2 : bignum`, we   *)
(* want to compute a bignum `bnadd z1 z2` s.t.                           *)
(*                                                                       *)
(*   bn2nat z = bn2nat z1 * b2nat z2                                     *)
(*                                                                       *)
(* Here, there exists numerous algorithms for computing the multipli-    *)
(* cation of two bignums, with different complexity (from quadratic to   *)
(* quasi-linear). Here, we are again going to use the school-book        *)
(* algorithm to implement the multiplication of bignums. It has a        *)
(* quadratic complexity and is then avoided in real-word bignum          *)
(* libraries:                                                            *)
(*                                                                       *)
(*   proc bnmul(z1 : bignum, z2 : bignum) : bignum {                     *)
(*     z : bignum <- [::]                                                *)
(*     for i = 0 to (size z2) - 1 {                                      *)
(*       z <- bnadd(z, bnshift(bnmul1(z1, z2_i), i))                     *)
(*     }                                                                 *)
(*     return z                                                          *)
(*   }                                                                   *)
(*                                                                       *)
(*   proc bnmul1(z : bignum, w : word) : bignum {                        *)
(*     aout  : bignum <- [::]                                            *)
(*     carry : word   <- 0                                               *)
(*                                                                       *)
(*     for i = 0 to (size z) - 1 {                                       *)
(*       w1, carry <- dword_mul_with_carry(z_i, w, carry)                *)
(*       aout <- aout ++ [:: w1]                                         *)
(*     }                                                                 *)
(*     if (carry != 0) {                                                 *)
(*       aout <- aout ++ [:: carry]                                      *)
(*     }                                                                 *)
(*   }                                                                   *)
(*                                                                       *)
(*  proc dword_mul_with_carry (w1 : word, w2 : word, carry : word) {     *)
(*    w1, w2 <- dword_mul(w1, w2)                                        *)
(*    c , w1 <- word_add_with_carry(w1, carry, false)                    *)
(*    if (c) {                                                           *)
(*      _, w2 <- word_add_with_carry(w2, 1, false)                       *)
(*    }                                                                  *)
(*    return (w1, w2)                                                    *)
(*  }                                                                    *)
(*                                                                       *)
(*  proc bnshift(w : bignum, n : nat) : bignum {                         *)
(*    for i = 0 to n-1 {                                                 *)
(*      w <- [:: 0] ++ w                                                 *)
(*    }                                                                  *)
(*    return w                                                           *)
(*                                                                       *)
(* where `dword_mul` does the double-word multiplication, whose speci-   *)
(* fication is given below.                                              *)

Context (dword_mul : word -> word -> word * word).

Axiom dword_mul_correct :
  forall (w1 w2 : word),
    let: (w'1, w'2) := dword_mul w1 w2 in
    nat_of_ord w1 * nat_of_ord w2 = w'1 + w'2 * wsize.

(* 6. Implement the functions `bnshift`, `dword_mul_with_carry`,         *)
(*    `bnmul1` & `bnmul`, using the pseudo-code implementations give     *)
(*    above.                                                             *)

Fixpoint bnshift (z : bignum) (n : nat) : bignum :=
  match n with
  | 0 => z
  | S m => [::(inord(0)) & (bnshift z m)]
  end.

Definition dword_mul_with_carry (w1 w2 c : word) : word * word :=
  let: (w1, w2) := dword_mul w1 w2 in
  let: (c, w1) := word_add_with_carry w1 c false in
  match c with
  | true =>
    let: (_, w2) := 
      word_add_with_carry w2 (inord(1)) false in (w1, w2)
  | false => (w1, w2)
  end.

Fixpoint bnmul1 (z:bignum) (w:word) : bignum := 
  match z with
  | nil => nil
  | z0::z_rest =>
    let: (res, c) := dword_mul z0 w in 
      res :: (bnadd ([::c]) (bnmul1 z_rest w))
  end.


Fixpoint bnmul (z1 z2 : bignum) : bignum :=
  match z2 with
  | nil => nil
  | z2_0::z2_rest =>
    bnadd (bnmul1 z1 z2_0) (bnshift (bnmul z1 z2_rest) 1)
  end.

(* 7. Prove the following arithmetical property about `bnshift`.         *)

Lemma pow_0 :
  forall (n:nat),
    n^0 = 1.

Proof.
trivial.
Qed.

Lemma mulnK :
  forall (n:nat) (m:nat) (k:nat),
    m=k -> n*(m) = n*(k).
Proof.
  intros.
  rewrite H.
  done.
Qed.

Lemma bnshiftE (z : bignum) (n : nat) :
  bn2nat (bnshift z n) = bn2nat z * (2^(n * (8 * size))).
Proof.
induction n.
simpl.
  rewrite mul0n.
  rewrite pow_0.
  rewrite muln1.
  done.

simpl.
  rewrite towordK.
  rewrite IHn.
  rewrite addn0.
  unfold wsize.
  simpl.
  
  rewrite (mulSn (n) (8 * size)).
  (* Search (_^(_ + _)). *)
  rewrite expnD.
  rewrite -mulnA.
  apply mulnK.
  apply mulnC.
  apply gt0_wsize.

Qed.

(* 8. Prove that `dword_mul_with_carry` implements a double-word         *)
(*    multiplication with carry, as stated below.                        *)


(* Useful Inequalities *)

Lemma subK : forall (n : nat) , n-n=0.
Proof.
induction n.
+ exact.
+ rewrite subSS.
  apply IHn.
Qed.

Axiom nat_nonneg : forall (a b : nat) ,
  a + b >= b.

Axiom lt_nat : forall (a b : nat),
  a < b -> a <= b-1.

Axiom simple_ineq : forall (a b : nat),
  a*b <= (b-1)*(b-1) -> a + 1 < b.

Lemma dword_mul_ineq (w1 w2 : word) :
  let (_, w3) := dword_mul w1 w2 in 
    nat_of_ord w3 + 1 < wsize.

Proof.

move e : (dword_mul w1 w2) => [c w3].
pose proof (dword_mul_correct w1 w2).
rewrite e in H; destruct e.

pose proof (ltn_nat_of_ord w1).
pose proof (ltn_nat_of_ord w2).

pose proof (lt_nat H0).
pose proof (lt_nat H1).

pose proof (nat_nonneg c (w3*wsize)) as H'.
rewrite -H in H'.

Search (_*_ <= _).

pose proof (leq_mul H2 H3).

Search (_ <= _ -> _ <= _).

pose proof (leq_trans H' H4).

apply simple_ineq in H5.
done.

Qed.


Lemma word_add_with_carry_ineq (w : word):
  (nat_of_ord w + 1 < wsize) ->
  let: (c, _) := word_add_with_carry w (inord(1)) false in 
    c = false.

Proof.

intros.
move e : (word_add_with_carry w (inord 1) false) => [c w'].
pose proof (word_add_with_carry_correct w (inord 1) false).
rewrite e in H0.
simpl in H0.
rewrite addn0 in H0.
rewrite inordK in H0.

destruct c.

simpl in H0.
rewrite H0 in H.
rewrite mul1n in H.
rewrite addnC in H.

Search (_+_ < _).
rewrite -ltn_subRL in H.
rewrite subK in H.
contradict H.

trivial.
trivial.
trivial.

Qed.

Lemma dword_mul_with_carry_correct (w1 w2 c : word) :
  let: (w'1, w'2) := dword_mul_with_carry w1 w2 c in
  bn2nat [:: w'1; w'2] = val w1 * val w2 + val c.
Proof.


move e : (dword_mul_with_carry w1 w2 c) => [w'1 w'2].
unfold dword_mul_with_carry in e.

move e1 : (dword_mul w1 w2) => [w''1 w''2] in e.

pose proof (dword_mul_ineq w1 w2) as H_ineq1.
rewrite e1 in H_ineq1.

pose proof (dword_mul_correct w1 w2) as H.
rewrite e1 in H; destruct e1.

pose proof (word_add_with_carry_correct w''1 c false).
move e2 : (word_add_with_carry w''1 c false) => [c' w] in H0.

simpl in H0.
rewrite addn0 in H0.

rewrite e2 in e.
destruct e2.

simpl.
rewrite mul0n.
rewrite add0n.

destruct c'.

(*== Case 2 is easier to solve ==*)

Focus 2.

inversion e; destruct e.
rewrite H3 in H.
rewrite H2 in H0.

rewrite H.

simpl in H0.
rewrite mul0n in H0.
rewrite addn0 in H0.

pose proof (addnC w''1 (w'2*wsize)).
rewrite H1.

pose proof (addnA (w'2 * wsize) w''1 c).
rewrite -H4.
rewrite H0.
done.

(*== Now we solve the other Case ==*)

move e2 : (word_add_with_carry w''2 (inord 1) false)  => [c' w'''2] in e.

pose proof (word_add_with_carry_ineq H_ineq1) as H_ineq2.
rewrite e2 in H_ineq2.

pose proof (word_add_with_carry_correct w''2 (inord 1) false).
rewrite e2 in H1.

inversion e; destruct e; destruct e2.

rewrite H4 in H1.
rewrite H3 in H0.

rewrite H_ineq2 in H1.
rewrite inordK in H1.
simpl in H1.
rewrite mul0n in H1.
rewrite addn0 in H1.
rewrite addn0 in H1.

simpl in H0.
rewrite mul1n in H0.

(*== Solving the Equation ==*)

rewrite H.
rewrite (addnC w''1 (w''2*wsize)).
rewrite -(addnA (w''2 * wsize) w''1 c).
rewrite H0.
rewrite addnA.

rewrite -H1.
ring.

trivial.

Qed.


(* 9. Prove that `bnmul1` implements a bignum by word multiplication,    *)
(*    as stated below.                                                   *)

Lemma mulDn :
  forall (a:nat) (b:nat) (c:nat) ,
    (a+b)*c = a*c + b*c.
Proof.
intros; ring.
Qed.

Lemma mulnD:
  forall (a:nat) (b:nat) (c:nat) ,
    a*(b+c) = a*b + a*c.
Proof.
intros; ring.
Qed.

Lemma bnmul1_correct (z : bignum) (w : word) :
  bn2nat (bnmul1 z w) = bn2nat z * val w.
Proof.

simpl.
move : w.
induction z.

intros; simpl.
rewrite mul0n; done.

intros; simpl.
move e : (dword_mul a w) => [res c].
simpl.

rewrite bnadd_correct.
simpl.
rewrite mul0n.
rewrite add0n.
rewrite IHz.

pose proof (dword_mul_correct a w).
rewrite e in H.

rewrite mulDn.
rewrite (mulDn (bn2nat z * wsize) a w).

rewrite H.
ring.

Qed.

(* 10. Prove the correctness of `bnmul`, as stated below.                *)

Lemma bnmul_correct (z1 z2 : bignum) :
  bn2nat (bnmul z1 z2) = bn2nat z1 * bn2nat z2.
Proof.
move : z1.
induction z2.
  
intros.
simpl.
rewrite muln0.
done.

intros.
simpl.
rewrite bnadd_correct.
rewrite bnmul1_correct.
simpl.

rewrite IHz2.
rewrite inordK.

rewrite addn0.
ring.

trivial.

Qed.