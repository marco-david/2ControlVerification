Require Import Lia.
Require Import QuantumLib.Permutations.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.VecSet.
Require Import QuantumLib.Polynomial.
Require Import QuantumLib.Quantum.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Classical_Prop.

(* ================================================================== *)
(* Helper: extract the k-th factor from a Cprod                       *)
(* ================================================================== *)

(* skip_seq f k removes element at position k:
   skip_seq f k i = f i      if i < k
   skip_seq f k i = f (i+1)  if i >= k  *)
Definition skip_seq (f : nat -> C) (k : nat) : nat -> C :=
  fun i => if (i <? k)%nat then f i else f (S i).

Lemma Cprod_extract_k : forall (n : nat) (f : nat -> C) (k : nat),
  (k < S n)%nat ->
  Cprod f (S n) = f k * Cprod (skip_seq f k) n.
Proof.
  induction n as [| n']; intros f k Hk.
  - (* n = 0, so k = 0 *)
    assert (k = 0%nat) by lia. subst.
    unfold Cprod, skip_seq. lca.
  - (* Cprod f (S (S n')) = Cprod f (S n') * f (S n') by definition *)
    bdestruct (k =? S n')%nat.
    + (* k is the last element *)
      subst.
      assert (Hceq : Cprod (skip_seq f (S n')) (S n') = Cprod f (S n')).
      { apply Cprod_eq_bounded; intros i Hi.
        unfold skip_seq. bdestruct (i <? S n')%nat; [reflexivity | lia]. }
      change (Cprod f (S (S n'))) with (Cprod f (S n') * f (S n')).
      rewrite Hceq. lca.
    + (* k < S n' *)
      assert (Hk' : (k < S n')%nat) by lia.
      change (Cprod f (S (S n'))) with (Cprod f (S n') * f (S n')).
      rewrite (IHn' f k Hk').
      (* skip_seq f k n' = f (S n') since n' >= k *)
      assert (Hss : skip_seq f k n' = f (S n')).
      { unfold skip_seq. bdestruct (n' <? k)%nat; [lia | reflexivity]. }
      rewrite <- Cprod_extend_r, Hss. ring.
Qed.

(* ================================================================== *)
(* Helper: Cprod = 0 iff some factor = 0                              *)
(* ================================================================== *)

Lemma Cprod_zero_some_factor : forall (n : nat) (f : nat -> C),
  Cprod f n = C0 ->
  exists k, (k < n)%nat /\ f k = C0.
Proof.
  intros n f Hprod.
  apply Classical_Prop.NNPP.
  intro HContra.
  assert (Hnnz : forall k, (k < n)%nat -> f k <> C0).
  { intros k Hk Hfk. apply HContra. exists k. split; assumption. }
  exact (Cprod_neq_0_bounded f n Hnnz Hprod).
Qed.

(* ================================================================== *)
(* Helper: continuity of c -> Cprod (c - a i) n                      *)
(* ================================================================== *)

Lemma cprod_sub_continuous : forall (n : nat) (a : nat -> C) (c0 : C),
  continuous_at (fun c => Cprod (fun i => c - a i) n) c0.
Proof.
  induction n as [| n']; intros a c0.
  - (* Base case: Cprod ... 0 = C1, constant function *)
    replace (fun c => Cprod (fun i : nat => c - a i) 0%nat) with (Peval [C1]).
    + exact (constant_continuous_poly C1 c0).
    + apply functional_extensionality; intro c. unfold Peval; simpl. lca.
  - (* Inductive case: Cprod (S n') = Cprod n' * (c - a n') *)
    replace (fun c => Cprod (fun i => c - a i) (S n')) with
            (fun c => Cprod (fun i => c - a i) n' * (c - a n')).
    + apply continuous_mult.
      * exact (IHn' a c0).
      * replace (fun c => c - a n') with (fun c => Peval [- a n'; C1] c).
        -- exact (polynomial_continuous [- a n'; C1] c0).
        -- apply functional_extensionality; intro c.
           unfold Peval; simpl. lca.
    + apply functional_extensionality; intro c. simpl. reflexivity.
Qed.

(* ================================================================== *)
(* Helper: equality for c != a0 extends to all c by continuity        *)
(* ================================================================== *)

Lemma cprod_sub_eq_all : forall (n : nat) (a b : nat -> C) (a0 : C),
  (forall c, c <> a0 ->
    Cprod (fun i => c - a i) n = Cprod (fun i => c - b i) n) ->
  forall c, Cprod (fun i => c - a i) n = Cprod (fun i => c - b i) n.
Proof.
  intros n a b a0 H c.
  destruct (Ceq_dec c a0) as [Heq | Hneq]; [subst | exact (H c Hneq)].
  assert (Hdiff_cont : continuous_at
      (fun c' => Cprod (fun i => c' - a i) n - Cprod (fun i => c' - b i) n) a0).
  { apply continuous_plus.
    - exact (cprod_sub_continuous n a a0).
    - replace (fun c' => - Cprod (fun i => c' - b i) n) with
              (fun c' => (-C1) * Cprod (fun i => c' - b i) n).
      + apply continuous_mult.
        * replace (fun _ : C => -C1) with (fun c' => Peval [-C1] c').
          -- exact (polynomial_continuous [-C1] a0).
          -- apply functional_extensionality; intro c'. unfold Peval; simpl. lca.
        * exact (cprod_sub_continuous n b a0).
      + apply functional_extensionality; intro c'. lca. }
  assert (Hdiff_zero : forall c', c' <> a0 ->
      Cprod (fun i => c' - a i) n - Cprod (fun i => c' - b i) n = C0).
  { intros c' Hc'. rewrite (H c' Hc'). lca. }
  pose proof (constant_ae_continuous _ C0 a0 Hdiff_cont Hdiff_zero) as Hlim.
  cbv beta in Hlim.
  exact (Cminus_eq_0 _ _ Hlim).
Qed.

(* ================================================================== *)
(* poly_roots_perm                                                     *)
(* ================================================================== *)

Lemma poly_roots_perm : forall (n : nat) (a b : nat -> C),
  (forall c, Cprod (fun i => c - a i) n = Cprod (fun i => c - b i) n) ->
  exists (σ : nat -> nat),
    permutation n σ /\ forall (i : nat), (i < n)%nat -> a i = b (σ i).
Proof.
  induction n as [| n']; intros a b Heq.
  - (* n = 0: identity permutation *)
    exists Datatypes.id.
    split; [apply id_permutation | intros i Hi; lia].
  - (* n = S n' *)
    (* Find k < S n' with b k = a n' *)
    assert (HaRoot : Cprod (fun j => a n' - b j) (S n') = C0).
    { rewrite <- (Heq (a n')).
      apply Cprod_0_bounded.
      exists n'. split; [lia | lca]. }
    apply Cprod_zero_some_factor in HaRoot.
    destruct HaRoot as (k & Hk & Hbk_zero).
    (* b k = a n' *)
    assert (Hbk : b k = a n').
    { exact (eq_sym (Cminus_eq_0 _ _ Hbk_zero)). }
    (* For c != a n', cancel (c - a n') from both sides *)
    assert (Hcprod_ne : forall c, c <> a n' ->
        Cprod (fun i => c - a i) n' =
        Cprod (fun j => c - skip_seq b k j) n').
    { intros c Hca.
      pose proof (Heq c) as HfullEq.
      assert (HLHS : Cprod (fun i => c - a i) (S n') =
                     Cprod (fun i => c - a i) n' * (c - a n')).
      { simpl. reflexivity. }
      assert (HRHS : Cprod (fun j => c - b j) (S n') =
                     (c - b k) * Cprod (fun j => c - skip_seq b k j) n').
      { rewrite (Cprod_extract_k n' (fun j => c - b j) k Hk).
        cbv beta. f_equal.
        apply Cprod_eq_bounded. intros i Hi.
        unfold skip_seq. bdestruct (i <? k)%nat; reflexivity. }
      rewrite HLHS, HRHS, Hbk in HfullEq.
      assert (Hca' : (c - a n') <> C0).
      { intro H'. exact (Hca (Cminus_eq_0 _ _ H')). }
      apply Cmult_cancel_r with (a := c - a n').
      - exact Hca'.
      - rewrite HfullEq. ring. }
    (* Extend to all c by continuity *)
    pose proof (cprod_sub_eq_all n' a (skip_seq b k) (a n') Hcprod_ne) as Hcprod_all.
    (* Apply inductive hypothesis *)
    destruct (IHn' a (skip_seq b k) Hcprod_all) as (σ' & Hperm' & Hroots').
    (* Construct σ: σ(n') = k, σ(i) = unskip(σ'(i), k) for i < n' *)
    exists (fun i => if (i =? n')%nat then k
                     else if (σ' i <? k)%nat then σ' i else S (σ' i)).
    split.
    + (* Prove permutation via surjectivity *)
      rewrite permutation_iff_surjective.
      intros j Hj.
      bdestruct (j =? k)%nat.
      * (* j = k: preimage is n' *)
        subst. exists n'. split; [lia |].
        bdestruct (n' =? n')%nat; [reflexivity | lia].
      * (* j != k: find preimage in {0,...,n'-1} *)
        set (j' := if (j <? k)%nat then j else (j - 1)%nat).
        assert (Hj'_lt : (j' < n')%nat).
        { unfold j'. bdestruct (j <? k)%nat; lia. }
        destruct (permutation_is_surjective n' σ' Hperm' j' Hj'_lt) as (i & Hi & Hσi).
        exists i. split; [lia |].
        bdestruct (i =? n')%nat; [lia |].
        rewrite Hσi.
        unfold j'.
        bdestruct (j <? k)%nat.
        -- bdestruct (j <? k)%nat; [reflexivity | lia].
        -- bdestruct ((j - 1) <? k)%nat; [lia | lia].
    + (* Prove the values match *)
      intros i Hi.
      bdestruct (i =? n')%nat.
      * subst. symmetry. exact Hbk.
      * assert (Hi' : (i < n')%nat) by lia.
        pose proof (Hroots' i Hi') as Hval.
        rewrite Hval.
        unfold skip_seq.
        bdestruct (σ' i <? k)%nat; reflexivity.
Qed.

(* ================================================================== *)
(* Determinant of (c*I - D) for diagonal D equals Cprod (c - D i i)  *)
(* ================================================================== *)

Lemma det_c_minus_diag : forall {n} (D : Square n) (c : C),
  WF_Diagonal D ->
  Determinant ((c .* I n) .+ ((-C1) .* D)) = Cprod (fun i => c - D i i) n.
Proof.
  intros n D c [WF_D Hdiag].
  rewrite det_up_tri_diags.
  - (* Show diagonal entries equal c - D i i *)
    apply Cprod_eq_bounded. intros i Hi.
    unfold Mplus, scale, I.
    rewrite Nat.eqb_refl.
    apply Nat.ltb_lt in Hi. rewrite Hi.
    lca.
  - (* Show (c*I - D) is upper triangular *)
    apply up_tri_plus.
    + apply up_tri_scale. apply up_tri_I.
    + apply up_tri_scale.
      unfold upper_triangular. intros i j Hij.
      apply Hdiag. lia.
Qed.

(* ================================================================== *)
(* Determinant is invariant under unitary conjugation                 *)
(* ================================================================== *)

Lemma det_unitary_conj : forall {n} (U M : Square n),
  WF_Unitary U ->
  Determinant (U × M × U†) = Determinant M.
Proof.
  intros n U M [WF_U HUU].
  (* From U† × U = I, derive U × U† = I *)
  assert (HUU' : U × U† = I n).
  { apply Minv_flip; auto with wf_db. }
  (* Det(U) * Det(U†) = 1 *)
  assert (Hdet : Determinant U * Determinant (U†) = C1).
  { rewrite Determinant_multiplicative, HUU'. apply Det_I. }
  (* Expand Det(U × M × U†) = Det(U) * Det(M) * Det(U†) *)
  repeat rewrite <- Determinant_multiplicative.
  replace (Determinant U * Determinant M * Determinant (U†)) with
          (Determinant M * (Determinant U * Determinant (U†))) by ring.
  rewrite Hdet. ring.
Qed.

(* ================================================================== *)
(* perm_eigenvalues                                                    *)
(* ================================================================== *)

Lemma perm_eigenvalues : forall {n} (U D D' : Square n),
  WF_Unitary U -> WF_Diagonal D -> WF_Diagonal D' -> U × D × U† = D' ->
  exists (σ : nat -> nat),
    permutation n σ /\ forall (i : nat), D i i = D' (σ i) (σ i).
Proof.
  intros n U D D' [WF_U HUU] HD HD' Heq.
  (* Derive U × U† = I n from U† × U = I n *)
  assert (HUU' : U × U† = I n).
  { apply Minv_flip; auto with wf_db. }
  (* Step 1: For all c, Det(c*I - D) = Det(c*I - D') *)
  assert (Hcprod : forall c,
      Cprod (fun i => c - D i i) n = Cprod (fun i => c - D' i i) n).
  { intro c.
    rewrite <- (det_c_minus_diag D c HD).
    rewrite <- (det_c_minus_diag D' c HD').
    (* (c*I - D') = U × (c*I - D) × U† *)
    assert (HcI : U × (c .* I n) × U† = c .* I n).
    { rewrite Mscale_mult_dist_r.
      rewrite Mmult_1_r; [| exact WF_U].
      rewrite Mscale_mult_dist_l, HUU'.
      reflexivity. }
    assert (HcD : U × ((-C1) .* D) × U† = (-C1) .* D').
    { rewrite Mscale_mult_dist_r, Mscale_mult_dist_l.
      f_equal. exact Heq. }
    assert (HcID : (c .* I n) .+ ((-C1) .* D') =
                    U × ((c .* I n) .+ ((-C1) .* D)) × U†).
    { rewrite Mmult_plus_distr_l, Mmult_plus_distr_r.
      rewrite HcI, HcD. reflexivity. }
    rewrite HcID. symmetry. apply det_unitary_conj. split; assumption. }
  (* Step 2: Apply poly_roots_perm *)
  destruct (poly_roots_perm n (fun i => D i i) (fun i => D' i i) Hcprod)
    as (σ & Hperm & Hroots).
  (* Extend σ to be the identity outside [0, n-1] so out-of-bounds indices
     also satisfy D i i = D' (σ i) (σ i) = 0 *)
  exists (fun i => if (i <? n)%nat then σ i else i).
  split.
  - (* Prove it is a permutation of [0, n-1] *)
    rewrite permutation_iff_surjective.
    intros j Hj.
    destruct (permutation_is_surjective n σ Hperm j Hj) as (i & Hi & Hσi).
    exists i. split; [exact Hi |].
    apply Nat.ltb_lt in Hi. rewrite Hi. exact Hσi.
  - (* Prove values match *)
    intros i. cbv beta.
    destruct (Nat.ltb i n) eqn:Heqb.
    + (* (i <? n) = true, so i < n *)
      apply Nat.ltb_lt in Heqb.
      exact (Hroots i Heqb).
    + (* (i <? n) = false, so i >= n: both D i i and D' i i are 0 by WF_Matrix *)
      assert (Hni : (n <= i)%nat) by (apply Nat.ltb_nlt in Heqb; lia).
      destruct HD as [WF_D _]. destruct HD' as [WF_D' _].
      rewrite (WF_D i i (or_introl Hni)).
      rewrite (WF_D' i i (or_introl Hni)).
      reflexivity.
Qed.

(* To equate the eigenvalues of two matrices, we often need equality of matrices
   up to some permutation. This lemma allows us to take the existence of a
   permutation on 4 elements and decompose it into the 24 possible cases. *)
Lemma permutation_4_decomp : forall (σ : nat -> nat),
  permutation 4 σ -> (
    (σ 0 = 0 /\ σ 1 = 1 /\ σ 2 = 2 /\ σ 3 = 3) \/
    (σ 0 = 0 /\ σ 1 = 1 /\ σ 2 = 3 /\ σ 3 = 2) \/
    (σ 0 = 0 /\ σ 1 = 2 /\ σ 2 = 1 /\ σ 3 = 3) \/
    (σ 0 = 0 /\ σ 1 = 2 /\ σ 2 = 3 /\ σ 3 = 1) \/
    (σ 0 = 0 /\ σ 1 = 3 /\ σ 2 = 1 /\ σ 3 = 2) \/
    (σ 0 = 0 /\ σ 1 = 3 /\ σ 2 = 2 /\ σ 3 = 1) \/
    (σ 0 = 1 /\ σ 1 = 0 /\ σ 2 = 2 /\ σ 3 = 3) \/
    (σ 0 = 1 /\ σ 1 = 0 /\ σ 2 = 3 /\ σ 3 = 2) \/
    (σ 0 = 1 /\ σ 1 = 2 /\ σ 2 = 0 /\ σ 3 = 3) \/
    (σ 0 = 1 /\ σ 1 = 2 /\ σ 2 = 3 /\ σ 3 = 0) \/
    (σ 0 = 1 /\ σ 1 = 3 /\ σ 2 = 0 /\ σ 3 = 2) \/
    (σ 0 = 1 /\ σ 1 = 3 /\ σ 2 = 2 /\ σ 3 = 0) \/
    (σ 0 = 2 /\ σ 1 = 0 /\ σ 2 = 1 /\ σ 3 = 3) \/
    (σ 0 = 2 /\ σ 1 = 0 /\ σ 2 = 3 /\ σ 3 = 1) \/
    (σ 0 = 2 /\ σ 1 = 1 /\ σ 2 = 0 /\ σ 3 = 3) \/
    (σ 0 = 2 /\ σ 1 = 1 /\ σ 2 = 3 /\ σ 3 = 0) \/
    (σ 0 = 2 /\ σ 1 = 3 /\ σ 2 = 0 /\ σ 3 = 1) \/
    (σ 0 = 2 /\ σ 1 = 3 /\ σ 2 = 1 /\ σ 3 = 0) \/
    (σ 0 = 3 /\ σ 1 = 0 /\ σ 2 = 1 /\ σ 3 = 2) \/
    (σ 0 = 3 /\ σ 1 = 0 /\ σ 2 = 2 /\ σ 3 = 1) \/
    (σ 0 = 3 /\ σ 1 = 1 /\ σ 2 = 0 /\ σ 3 = 2) \/
    (σ 0 = 3 /\ σ 1 = 1 /\ σ 2 = 2 /\ σ 3 = 0) \/
    (σ 0 = 3 /\ σ 1 = 2 /\ σ 2 = 0 /\ σ 3 = 1) \/
    (σ 0 = 3 /\ σ 1 = 2 /\ σ 2 = 1 /\ σ 3 = 0)
  )%nat.
Proof.
  assert (perm_values : forall {n} (σ : nat -> nat),
    permutation n σ ->
      let N : Ensemble nat := (fun x => x < n)%nat in
      forall (i : nat),
        (i < n)%nat ->
          let Image := (fun x => exists (j : nat), (j < i)%nat /\ σ j = x) in
          In nat (Setminus nat N Image) (σ i)).
  {
    intros n σ permutation_σ N i i_lt_n Image.
    unfold Setminus, In, N, Image.
    split.
    {
      destruct permutation_σ as [σ_inv H].
      apply H.
      assumption.
    }
    {
      apply all_not_not_ex.
      intros m [m_lt_i σm_eq_σi].
      assert (m_lt_n : (m < n)%nat) by lia.
      pose proof (
        permutation_is_injective n σ permutation_σ m i m_lt_n i_lt_n σm_eq_σi
      ) as m_eq_i.
      lia.
    }
  }
  intros σ permutation_σ.
  pose proof (perm_values 4%nat σ permutation_σ) as perm_helper.

  specialize (perm_helper 0%nat) as perm_helper_0.
  destruct perm_helper_0 as [σ0_lt_4 _]; auto; unfold In in σ0_lt_4.

  specialize (perm_helper 1%nat) as perm_helper_1.
  destruct perm_helper_1 as [σ1_lt_4 help0]; auto; unfold In in σ1_lt_4.
  unfold In in help0.
  pose proof (not_ex_all_not _ _ help0) as helper0; clear help0.
  specialize (helper0 0%nat) as σ0_neq_σ1; clear helper0.
  revert σ0_neq_σ1; simpl; intro σ0_neq_σ1.
  apply not_and_or in σ0_neq_σ1.
  destruct σ0_neq_σ1 as [absurd | σ0_neq_σ1]. lia.

  specialize (perm_helper 2%nat) as perm_helper_2.
  destruct perm_helper_2 as [σ2_lt_4 help1]; auto; unfold In in σ2_lt_4.
  unfold In in help1.
  pose proof (not_ex_all_not _ _ help1) as helper1; clear help1.
  specialize (helper1 0%nat) as σ0_neq_σ2.
  specialize (helper1 1%nat) as σ1_neq_σ2; clear helper1.
  revert σ0_neq_σ2 σ1_neq_σ2. simpl. intros σ0_neq_σ2 σ1_neq_σ2.
  apply not_and_or in σ0_neq_σ2, σ1_neq_σ2.
  destruct σ0_neq_σ2 as [absurd | σ0_neq_σ2]. lia.
  destruct σ1_neq_σ2 as [absurd | σ1_neq_σ2]. lia.

  specialize (perm_helper 3%nat) as perm_helper_3.
  destruct perm_helper_3 as [σ3_lt_4 help2]; auto; unfold In in σ3_lt_4.
  unfold In in help2.
  pose proof (not_ex_all_not _ _ help2) as helper2; clear help2.
  specialize (helper2 0%nat) as σ0_neq_σ3.
  specialize (helper2 1%nat) as σ1_neq_σ3.
  specialize (helper2 2%nat) as σ2_neq_σ3; clear helper2.
  revert σ0_neq_σ3 σ1_neq_σ3 σ2_neq_σ3. simpl. intros σ0_neq_σ3 σ1_neq_σ3 σ2_neq_σ3.
  apply not_and_or in σ0_neq_σ3, σ1_neq_σ3, σ2_neq_σ3.
  destruct σ0_neq_σ3 as [absurd | σ0_neq_σ3]. lia.
  destruct σ1_neq_σ3 as [absurd | σ1_neq_σ3]. lia.
  destruct σ2_neq_σ3 as [absurd | σ2_neq_σ3]. lia.
  destruct (σ 0%nat).
  {
    destruct (σ 1%nat); try contradiction.
    destruct n.
    {
      destruct (σ 2%nat); try contradiction.
      destruct n; try contradiction.
      destruct n.
      {
        destruct (σ 3%nat); try contradiction.
        destruct n; try contradiction.
        destruct n; try contradiction.
        destruct n; try lia.
      }
      {
        destruct n; try lia.
      }
    }
    {
      destruct n.
      {
        destruct (σ 2%nat); try contradiction.
        destruct n.
        {
          destruct (σ 3%nat); try contradiction.
          destruct n; try contradiction.
          destruct n; try contradiction.
          destruct n; try lia.
        }
        {
          destruct n; try contradiction.
          destruct n; try lia.
        }
      }
      {
        destruct n; try lia.
      }
    }
  }
  {
    destruct n.
    {
      destruct (σ 1%nat).
      {
        destruct (σ 2%nat); try contradiction.
        destruct n; try contradiction.
        destruct n.
        {
          destruct (σ 3%nat); try contradiction.
          destruct n; try contradiction.
          destruct n; try contradiction.
          destruct n; try lia.
        }
        {
          destruct n; try lia.
        }
      }
      {
        destruct n; try contradiction.
        destruct n.
        {
          destruct (σ 2%nat); try contradiction.
          {
            destruct (σ 3%nat); try contradiction.
            destruct n; try contradiction.
            destruct n; try contradiction.
            destruct n; try lia.
          }
          {
            destruct n; try contradiction.
            destruct n; try contradiction.
            destruct n; try lia.
          }
        }
        {
          destruct n; try lia.
        }
      }
    }
    {
      destruct n.
      {
        destruct (σ 1%nat).
        {
          destruct (σ 2%nat); try contradiction.
          destruct n.
          {
            destruct (σ 3%nat); try contradiction.
            destruct n; try contradiction.
            destruct n; try contradiction.
            destruct n; try lia.
          }
          {
            destruct n; try contradiction.
            destruct n; try lia.
          }
        }
        {
          destruct n.
          {
            destruct (σ 2%nat).
            {
              destruct (σ 3%nat); try contradiction.
              destruct n; try contradiction.
              destruct n; try contradiction.
              destruct n; try lia.
            }
            {
              destruct n; try contradiction.
              destruct n; try contradiction.
              destruct n; try lia.
            }
          }
          {
            destruct n; try contradiction.
            destruct n; try lia.
          }
        }
      }
      {
        destruct n. 2: { exfalso. lia. }
        destruct (σ 1%nat).
        {
          destruct (σ 2%nat); try contradiction.
          destruct n.
          {
            destruct (σ 3%nat); try contradiction.
            destruct n; try contradiction.
            destruct n; try lia.
          }
          {
            destruct n; try lia.
          }
        }
        {
          destruct n.
          {
            destruct (σ 2%nat).
            {
              destruct (σ 3%nat); try contradiction.
              destruct n; try contradiction.
              destruct n; try lia.
            }
            {
              destruct n; try contradiction.
              destruct n; try lia.
            }
          }
          {
            destruct n; try lia.
          }
        }
      }
    }
  }
Qed.

(* Helper tactic to quickly destruct cases and assign them a uniform name *)
Ltac destruct_disjunctions name :=
  match goal with
  | [ H : _ \/ _ |- _ ] => destruct H as [name | H]; destruct_disjunctions name
  | _ => idtac
  end.
