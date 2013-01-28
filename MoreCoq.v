(** * MoreCoq: More About Coq *)

Require Export Poly.

(* ###################################################### *)
(** * More About Coq *)
     
(* ###################################################### *)
(** ** The [apply] Tactic *)

(** We often encounter situations where the goal to be proved is
    exactly the same as some hypothesis in the context or some
    previously proved lemma. *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n,o] = [n,p] ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* At this point, we could finish with "[rewrite -> eq2. reflexivity.]"
     as we have done several times above. But we can achieve the 
     same effect in a single step by using the [apply] tactic instead: *)
  apply eq2.  Qed.

(** The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2. 
  apply eq2. apply eq1.  Qed.

(** You may find it instructive to experiment with this proof
    and see if there is a way to complete it using just [rewrite]
    instead of [apply]. *)

(** Typically, when we use [apply H], the statement [H] will
    begin with a [forall] binding some _universal variables_.  When
    Coq matches the current goal against the conclusion of [H], it
    will try to find appropriate values for these variables.  For
    example, when we do [apply eq2] in the following proof, the
    universal variable [q] in [eq2] gets instantiated with [n] and [r]
    gets instantiated with [m]. *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** **** Exercise: 2 stars, optional (silly_ex) *)
(** Complete the following proof without using [simpl]. *)

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal _exactly_ -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  (* Here we cannot use [apply] directly *)
Admitted.

(** In this case we can use the [symmetry] tactic, which
    switches the left and right sides of an equality in the goal. *)

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* Actually, this [simpl] is unnecessary, since 
            [apply] will do a [simpl] step first. *)  
  apply H.  Qed.         

(** **** Exercise: 3 stars (apply_exercise1) *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  (* Hint: you can use [apply] with previously defined lemmas, not
     just hypotheses in the context.  Remember that [SearchAbout] is
     your friend. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (apply_rewrite) *)
(** Briefly explain the difference between the tactics [apply] and
    [rewrite].  Are there situations where both can usefully be
    applied?

  (* FILL IN HERE *)
*)
(** [] *)

(* ###################################################### *)
(** ** Inversion *)

(** Recall the definition of natural numbers:
     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.
    It is clear from this definition that every number has one of two
    forms: either it is the constructor [O] or it is built by applying
    the constructor [S] to another number.  But there is more here than
    meets the eye: implicit in the definition (and in our informal
    understanding of how datatype declarations work in other
    programming languages) are two other facts:

    - The constructor [S] is _injective_.  That is, the only way we can
      have [S n = S m] is if [n = m].

    - The constructors [O] and [S] are _disjoint_.  That is, [O] is not
      equal to [S n] for any [n]. *)

(** Similar principles apply to all inductively defined types: all
    constructors are injective, and the values built from distinct
    constructors are never equal.  For lists, the [cons] constructor is
    injective and [nil] is different from every non-empty list.  For
    booleans, [true] and [false] are unequal.  (Since neither [true]
    nor [false] take any arguments, their injectivity is not an issue.) *)

(** Coq provides a tactic, called [inversion], that allows us to
    exploit these principles in making proofs.
 
    The [inversion] tactic is used like this.  Suppose [H] is a
    hypothesis in the context (or a previously proven lemma) of the
    form
      c a1 a2 ... an = d b1 b2 ... bm
    for some constructors [c] and [d] and arguments [a1 ... an] and
    [b1 ... bm].  Then [inversion H] instructs Coq to "invert" this
    equality to extract the information it contains about these terms:

    - If [c] and [d] are the same constructor, then we know, by the
      injectivity of this constructor, that [a1 = b1], [a2 = b2],
      etc.; [inversion H] adds these facts to the context, and tries
      to use them to rewrite the goal.

    - If [c] and [d] are different constructors, then the hypothesis
      [H] is contradictory.  That is, a false assumption has crept
      into the context, and this means that any goal whatsoever is
      provable!  In this case, [inversion H] marks the current goal as
      completed and pops it off the goal stack. *)

(** The [inversion] tactic is probably easier to understand by
    seeing it in action than from general descriptions like the above.
    Below you will find example theorems that demonstrate the use of
    [inversion] and exercises to test your understanding. *)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.  Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity.  Qed.

(** As a convenience, the [inversion] tactic can also
    destruct equalities between complex values, binding
    multiple variables as it goes. *)

Theorem silly5 : forall (n m o : nat),
     [n,m] = [o,o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

(** **** Exercise: 1 star (sillyex1) *) 
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra.  Qed.

(** **** Exercise: 1 star (sillyex2) *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** While the injectivity of constructors allows us to reason
    [forall (n m : nat), S n = S m -> n = m], the reverse direction of
    the implication, provable by standard equational reasoning, is a
    useful fact to record for cases we will see several times. *)

Lemma eq_remove_S : forall n m,
  n = m -> S n = S m.
Proof. intros n m eq. rewrite -> eq. reflexivity. Qed.

(** Here's another illustration of [inversion].  This is a slightly
    roundabout way of stating a fact that we have already proved
    above.  The extra equalities force us to do a little more
    equational reasoning and exercise some of the tactics we've seen
    recently. *)

Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros X v l. induction l as [| v' l'].
  Case "l = []". intros n eq. rewrite <- eq. reflexivity.
  Case "l = v' :: l'". intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply eq_remove_S. apply IHl'. inversion eq. reflexivity. Qed.

(* ###################################################### *)
(** ** Varying the Induction Hypothesis *)

(** Here is a more realistic use of inversion to prove a
    property that is useful in many places later on... *)

Theorem beq_nat_eq_FAILED : forall n m,
  true = beq_nat n m -> n = m.
Proof.
  intros n m H. induction n as [| n']. 
  Case "n = 0".
    destruct m as [| m'].
    SCase "m = 0". reflexivity.  
    SCase "m = S m'". simpl in H. inversion H. 
  Case "n = S n'".
    destruct m as [| m'].
    SCase "m = 0". simpl in H. inversion H.
    SCase "m = S m'".
      apply eq_remove_S. 
      (* stuck here because the induction hypothesis
         talks about an extremely specific m *)
      Admitted.

(** The inductive proof above fails because we've set up things so
    that the induction hypothesis (in the second subgoal generated by
    the [induction] tactic) is

       [ true = beq_nat n' m -> n' = m ].

     This hypothesis makes a statement about [n'] together with the
     _particular_ natural number [m] -- that is, the number [m], which
     was introduced into the context by the [intros] at the top of the
     proof, is "held constant" in the induction hypothesis.  This
     induction hypothesis is not strong enough to make the induction
     step of the proof go through.

     If we set up the proof slightly differently by introducing just
     [n] into the context at the top, then we get an induction
     hypothesis that makes a stronger claim:

      [ forall m : nat, true = beq_nat n' m -> n' = m ]

     Setting up the induction hypothesis this way makes the proof of
     [beq_nat_eq] go through: *)

Theorem beq_nat_eq : forall n m,
  true = beq_nat n m -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". 
    intros m. destruct m as [| m'].
    SCase "m = 0". reflexivity.  
    SCase "m = S m'". simpl. intros contra. inversion contra. 
  Case "n = S n'".
    intros m. destruct m as [| m'].
    SCase "m = 0". simpl. intros contra. inversion contra.
    SCase "m = S m'". simpl. intros H.
      apply eq_remove_S. apply IHn'. apply H. Qed.

(** Similar issues will come up in _many_ of the proofs below.  If you
    ever find yourself in a situation where the induction hypothesis
    is insufficient to establish the goal, consider going back and
    doing fewer [intros] to make the IH stronger. *)

(** **** Exercise: 2 stars, advanced (beq_nat_eq_informal) *)
(** Give an informal proof of [beq_nat_eq]. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars (beq_nat_eq') *)
(** We can also prove beq_nat_eq by induction on [m], though we have
    to be a little careful about which order we introduce the
    variables, so that we get a general enough induction hypothesis --
    this is done for you below.  Finish the following proof.  To get
    maximum benefit from the exercise, try first to do it without
    looking back at the one above. *)

Theorem beq_nat_eq' : forall m n,
  beq_nat n m = true -> n = m.
Proof.
  intros m. induction m as [| m']. 
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################### *)
(** *** Practice Session *)

(** **** Exercise: 2 stars, optional (practice) *)
(** Some nontrivial but not-too-complicated proofs to work together in
    class, and some for you to work as exercises.  Some of the
    exercises may involve applying lemmas from earlier lectures or
    homeworks. *)
 

Theorem beq_nat_0_l : forall n,
  true = beq_nat 0 n -> 0 = n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem beq_nat_0_r : forall n,
  true = beq_nat 0 n -> 0 = n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (apply_exercise2) *)
(** In the following proof opening, notice that we don't introduce [m]
    before performing induction.  This leaves it general, so that the
    IH doesn't specify a particular [m], but lets us pick.  Finish the
    proof. *)

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [| n'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (beq_nat_sym_informal) *)
(** Provide an informal proof of this lemma that corresponds
    to your formal proof above:

   Theorem: For any [nat]s [n] [m], [beq_nat n m = beq_nat m n].

   Proof:
   (* FILL IN HERE *)
[]
 *)

(* ###################################################### *)
(** ** Using Tactics on Hypotheses *)

(** By default, most tactics work on the goal formula and leave
    the context unchanged.  However, most tactics also have a variant
    that performs a similar operation on a statement in the context.

    For example, the tactic [simpl in H] performs simplification in
    the hypothesis named [H] in the context. *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b. 
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** Similarly, the tactic [apply L in H] matches some
    conditional statement [L] (of the form [L1 -> L2], say) against a
    hypothesis [H] in the context.  However, unlike ordinary
    [apply] (which rewrites a goal matching [L2] into a subgoal [L1]),
    [apply L in H] matches [H] against [L1] and, if successful,
    replaces it with [L2].
 
    In other words, [apply L in H] gives us a form of "forward
    reasoning" -- from [L1 -> L2] and a hypothesis matching [L1], it
    gives us a hypothesis matching [L2].  By contrast, [apply L] is
    "backward reasoning" -- it says that if we know [L1->L2] and we
    are trying to prove [L2], it suffices to prove [L1].  

    Here is a variant of a proof from above, using forward reasoning
    throughout instead of backward reasoning. *)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5  ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H. 
  apply H.  Qed.

(** Forward reasoning starts from what is _given_ (premises,
    previously proven theorems) and iteratively draws conclusions from
    them until the goal is reached.  Backward reasoning starts from
    the _goal_, and iteratively reasons about what would imply the
    goal, until premises or previously proven theorems are reached.
    If you've seen informal proofs before (for example, in a math or
    computer science class), they probably used forward reasoning.  In
    general, Coq tends to favor backward reasoning, but in some
    situations the forward style can be easier to use or to think
    about.  *)

(** **** Exercise: 3 stars (plus_n_n_injective) *)
(** You can practice using the "in" variants in this exercise. *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    (* Hint: use the plus_n_Sm lemma *)
    (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** Using [destruct] on Compound Expressions *)

(** We have seen many examples where the [destruct] tactic is
    used to perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [destruct].

    Here are some examples: *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun. 
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity.  Qed.

(** After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if (beq_nat n 3) then ... else ...].  Well,
    either [n] is equal to [3] or it isn't, so we use [destruct
    (beq_nat n 3)] to let us reason about the two cases. *)

(** **** Exercise: 1 star (override_shadow) *)
Theorem override_shadow : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (combine_split) *)
(* 
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| [x y] l'].
  (* FILL IN HERE *) Admitted.
*)
(** [] *)

(** **** Exercise: 3 stars (split_combine) *)
(** Thought exercise: We have just proven that for all lists of pairs,
    [combine] is the inverse of [split].  How would you state the
    theorem showing that [split] is the inverse of [combine]?
 
    Hint: what property do you need of [l1] and [l2] for [split]
    [combine l1 l2 = (l1,l2)] to be true?

    State this theorem in Coq, and prove it. (Be sure to leave your
    induction hypothesis general by not doing [intros] on more things
    than necessary.) *)

(* FILL IN HERE *) 
(** [] *)

(* ###################################################### *)
(** ** The [remember] Tactic *)

(** (Note: the [remember] tactic is not strictly needed until a
    bit later, so if necessary this section can be skipped and
    returned to when needed.) *)

(** We have seen how the [destruct] tactic can be used to
    perform case analysis of the results of arbitrary computations.
    If [e] is an expression whose type is some inductively defined
    type [T], then, for each constructor [c] of [T], [destruct e]
    generates a subgoal in which all occurrences of [e] (in the goal
    and in the context) are replaced by [c].

    Sometimes, however, this substitution process loses information
    that we need in order to complete the proof.  For example, suppose
    we define a function [sillyfun1] like this: *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(** And suppose that we want to convince Coq of the rather
    obvious observation that [sillyfun1 n] yields [true] only when [n]
    is odd.  By analogy with the proofs we did with [sillyfun] above,
    it is natural to start the proof like this: *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* stuck... *)
Admitted.

(** We get stuck at this point because the context does not
    contain enough information to prove the goal!  The problem is that
    the substitution peformed by [destruct] is too brutal -- it threw
    away every occurrence of [beq_nat n 3], but we need to keep at
    least one of these because we need to be able to reason that
    since, in this branch of the case analysis, [beq_nat n 3 = true],
    it must be that [n = 3], from which it follows that [n] is odd.

    What we would really like is not to use [destruct] directly on
    [beq_nat n 3] and substitute away all occurrences of this
    expression, but rather to use [destruct] on something else that is
    _equal_ to [beq_nat n 3].  For example, if we had a variable that
    we knew was equal to [beq_nat n 3], we could [destruct] this
    variable instead.

    The [remember] tactic allows us to introduce such a variable. *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
   remember (beq_nat n 3) as e3.
   (* At this point, the context has been enriched with a new
      variable [e3] and an assumption that [e3 = beq_nat n 3].
      Now if we do [destruct e3]... *)
   destruct e3.
   (* ... the variable [e3] gets substituted away (it
     disappears completely) and we are left with the same
      state as at the point where we got stuck above, except
      that the context still contains the extra equality
      assumption -- now with [true] substituted for [e3] --
      which is exactly what we need to make progress. *)
     Case "e3 = true". apply beq_nat_eq in Heqe3.
       rewrite -> Heqe3. reflexivity.
     Case "e3 = false".
      (* When we come to the second equality test in the
        body of the function we are reasoning about, we can
         use [remember] again in the same way, allowing us
         to finish the proof. *)
       remember (beq_nat n 5) as e5. destruct e5.
         SCase "e5 = true".
           apply beq_nat_eq in Heqe5.
           rewrite -> Heqe5. reflexivity.
         SCase "e5 = false". inversion eq.  Qed.

(** **** Exercise: 2 stars *)
Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (override_same) *)
Theorem override_same : forall {X:Type} x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override f k1 x1) k2 = f k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (filter_exercise) *)
(** This one is a bit challenging.  Be sure your initial [intros] go
    only up through the parameter on which you want to do
    induction! *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** The [apply ... with ...] Tactic *)

(** The following silly example uses two rewrites in a row to
    get from [[a,b]] to [[e,f]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a,b] = [c,d] ->
     [c,d] = [e,f] ->
     [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** Since this is a common pattern, we might
    abstract it out as a lemma recording once and for all
    the fact that equality is transitive. *)

Theorem trans_eq : forall {X:Type} (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2. 
  reflexivity.  Qed.

(** Now, we should be able to use [trans_eq] to
    prove the above example.  However, to do this we need
    a slight refinement of the [apply] tactic. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a,b] = [c,d] ->
     [c,d] = [e,f] ->
     [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2. 
  (* If we simply tell Coq [apply trans_eq] at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate [X]
     with [[nat]], [n] with [[a,b]], and [o] with [[e,f]].
     However, the matching process doesn't determine an
     instantiation for [m]: we have to supply one explicitly
     by adding [with (m:=[c,d])] to the invocation of
     [apply]. *)
  apply trans_eq with (m:=[c,d]). apply eq1. apply eq2.   Qed.

(**  Actually, we usually don't have to include the name [m]
    in the [with] clause; Coq is often smart enough to
    figure out which instantiation we're giving. We could
    instead write: apply trans_eq with [c,d]. *)

(** **** Exercise: 3 stars (apply_exercises) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o). 
Proof.
  (* FILL IN HERE *) Admitted.

Theorem beq_nat_trans : forall n m p,
  true = beq_nat n m ->
  true = beq_nat m p ->
  true = beq_nat n p.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem override_permute : forall {X:Type} x1 x2 k1 k2 k3 (f : nat->X),
  false = beq_nat k2 k1 ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################## *)
(** * Review *)

(** We've now seen a bunch of Coq's fundamental tactics -- enough to
    do pretty much everything we'll want for a while.  We'll introduce
    one or two more as we go along through the next few lectures, and
    later in the course we'll introduce some more powerful
    _automation_ tactics that make Coq do more of the low-level work
    in many cases.  But basically we've got what we need to get work
    done.

    Here are the ones we've seen:

      - [intros]: 
        move hypotheses/variables from goal to context 

      - [reflexivity]:
        finish the proof (when the goal looks like [e = e])

      - [apply]:
        prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: 
        apply a hypothesis, lemma, or constructor to a hypothesis in
        the context (forward reasoning)

      - [apply... with...]:
        explicitly specify values for variables that cannot be
        determined by pattern matching

      - [simpl]:
        simplify computations in the goal 

      - [simpl in H]:
        ... or a hypothesis 

      - [rewrite]:
        use an equality hypothesis (or lemma) to rewrite the goal 

      - [rewrite ... in H]:
        ... or a hypothesis 

      - [symmetry]:
        changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]:
        changes a hypothesis of the form [t=u] into [u=t]

      - [unfold]:
        replace a defined constant by its right-hand side in the goal 

      - [unfold... in H]:
        ... or a hypothesis  

      - [destruct... as...]:
        case analysis on values of inductively defined types 

      - [induction... as...]:
        induction on values of inductively defined types 

      - [inversion]:
        reason by injectivity and distinctness of constructors

      - [remember (e) as x]:
        give a name ([x]) to an expression ([e]) so that we can
        destruct [x] without "losing" [e]

      - [assert (e) as H]:
        introduce a "local lemma" [e] and call it [H] 
*)

(* ###################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars (forall_exists_challenge) *)
(** Challenge problem: Define two recursive [Fixpoints],
    [forallb] and [existsb].  The first checks whether every
    element in a list satisfies a given predicate:
      forallb oddb [1,3,5,7,9] = true

      forallb negb [false,false] = true
  
      forallb evenb [0,2,4,5] = false
  
      forallb (beq_nat 5) [] = true
    The function [existsb] checks whether there exists an element in
    the list that satisfies a given predicate:
      existsb (beq_nat 5) [0,2,3,6] = false
 
      existsb (andb true) [true,true,false] = true
 
      existsb oddb [1,0,0,0,0,3] = true
 
      existsb evenb [] = false
    Next, create a _nonrecursive_ [Definition], [existsb'], using
    [forallb] and [negb].
 
    Prove that [existsb'] and [existsb] have the same behavior.
*)

(* FILL IN HERE *)
(** [] *)


(* $Date: 2013-01-22 11:34:02 -0500 (Tue, 22 Jan 2013) $ *)

