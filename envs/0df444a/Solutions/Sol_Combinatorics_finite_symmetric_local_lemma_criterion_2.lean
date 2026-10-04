-- Prove2me | solution 2 for Combinatorics.finite_symmetric_local_lemma_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:32:20.71189+00:00
-- url     : https://prove2.me/submissions/639d6c18-a3c9-44ca-a4ad-4ee965582d7a

import Mathlib

set_option autoImplicit false

namespace P2M7ce7e904

universe u v

variable {Omega : Type u} {I : Type v} [Fintype Omega] [DecidableEq Omega] [DecidableEq I]

/-- outcomes avoiding every event indexed by `S` -/
def av (A : I → Finset Omega) (S : Finset I) : Finset Omega :=
  Finset.univ.filter (fun w => ∀ j, j ∈ S → ¬ w ∈ A j)

/-- conditional bound `P(A_i | avoid U) ≤ x`, in multiplicative form -/
def CB (A : I → Finset Omega) (x : ℝ) (U : Finset I) : Prop :=
  ∀ i, i ∉ U → ((((av A U).filter (fun w => w ∈ A i)).card : ℕ) : ℝ) ≤ x * ((av A U).card : ℝ)

lemma av_insert (A : I → Finset Omega) (j : I) (U : Finset I) :
    av A (insert j U) = (av A U).filter (fun w => ¬ w ∈ A j) := by
  ext w
  simp only [av, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    exact ⟨fun k hk => h k (Or.inr hk), h j (Or.inl rfl)⟩
  · rintro ⟨h1, h2⟩ k hk
    rcases hk with rfl | hk
    · exact h2
    · exact h1 k hk

lemma av_mono (A : I → Finset Omega) {U V : Finset I} (h : U ⊆ V) : av A V ⊆ av A U := by
  intro w hw
  simp only [av, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  exact fun k hk => hw k (h hk)

lemma av_empty (A : I → Finset Omega) : av A (∅ : Finset I) = Finset.univ := by
  ext w
  simp [av]

lemma grow (A : I → Finset Omega) (x : ℝ) (hx1 : x ≤ 1) (m : ℕ)
    (hC : ∀ V : Finset I, V.card < m → CB A x V) :
    ∀ T U : Finset I, Disjoint T U → (T ∪ U).card ≤ m →
      (1 - x) ^ T.card * ((av A U).card : ℝ) ≤ ((av A (T ∪ U)).card : ℝ) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro U _ _
    simp
  | insert j T hj ih =>
    intro U hd hcard
    have hjU : j ∉ U := by
      intro h
      exact Finset.disjoint_left.mp hd (Finset.mem_insert_self j T) h
    have hdT : Disjoint T U := Finset.disjoint_of_subset_left (Finset.subset_insert j T) hd
    have hjTU : j ∉ T ∪ U := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hj, hjU⟩
    have heq : insert j T ∪ U = insert j (T ∪ U) := Finset.insert_union j T U
    have hcTU : (T ∪ U).card < m := by
      rw [heq, Finset.card_insert_of_notMem hjTU] at hcard
      omega
    have hcTU' : (T ∪ U).card ≤ m := le_of_lt hcTU
    have ih' := ih U hdT hcTU'
    have hCB := hC (T ∪ U) hcTU j hjTU
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := av A (T ∪ U)) (fun w => w ∈ A j)
    rw [heq, av_insert, Finset.card_insert_of_notMem hj, pow_succ]
    have hsplit' : ((((av A (T ∪ U)).filter (fun w => w ∈ A j)).card : ℕ) : ℝ)
        + ((((av A (T ∪ U)).filter (fun w => ¬ w ∈ A j)).card : ℕ) : ℝ)
        = ((av A (T ∪ U)).card : ℝ) := by
      exact_mod_cast hsplit
    have h1x : 0 ≤ 1 - x := by linarith
    have : (1 - x) ^ T.card * (1 - x) * ((av A U).card : ℝ)
        = (1 - x) * ((1 - x) ^ T.card * ((av A U).card : ℝ)) := by ring
    rw [this]
    calc (1 - x) * ((1 - x) ^ T.card * ((av A U).card : ℝ))
        ≤ (1 - x) * ((av A (T ∪ U)).card : ℝ) := mul_le_mul_of_nonneg_left ih' h1x
      _ ≤ _ := by linarith

end P2M7ce7e904

open P2M7ce7e904 in
theorem P2M7ce7e904.crit
    (Omega I : Type*) [Fintype Omega] [Nonempty Omega] [DecidableEq Omega]
    [Fintype I] [DecidableEq I]
    (A : I -> Finset Omega) (dep : I -> I -> Prop) [DecidableRel dep]
    (x : Real) (hx0 : 0 <= x) (hx1 : x < 1)
    (hprob : forall i,
      ((A i).card : Real) / (Fintype.card Omega : Real) <=
        x * (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card)
    (hindependent : forall (i : I) (S : Finset I),
      (forall j, Membership.mem S j -> Not (dep i j)) ->
      ((Finset.filter (fun w => Membership.mem (A i) w)
          (Finset.univ.filter (fun w => forall j, Membership.mem S j ->
            Not (Membership.mem (A j) w)))).card : Real) /
          (Fintype.card Omega : Real) =
        (((Finset.univ.filter (fun w => forall j, Membership.mem S j ->
            Not (Membership.mem (A j) w))).card : Real) /
            (Fintype.card Omega : Real)) *
          ((A i).card : Real) / (Fintype.card Omega : Real)) :
    Exists fun w : Omega => forall i, Not (Membership.mem (A i) w) := by
  have hN : (0 : ℝ) < (Fintype.card Omega : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h1x : 0 < 1 - x := by linarith
  -- the key step: conditional bound for every S
  have key : ∀ S : Finset I, (∀ V : Finset I, V.card < S.card → CB A x V) → CB A x S := by
    intro S hC i hi
    set S1 := S.filter (fun j => dep i j) with hS1
    set S2 := S.filter (fun j => ¬ dep i j) with hS2
    have hU : S1 ∪ S2 = S := Finset.filter_union_filter_not_eq _ _
    have hD : Disjoint S1 S2 := Finset.disjoint_filter_filter_not _ _ _
    have hgrow := grow A x (le_of_lt hx1) S.card hC S1 S2 hD (by rw [hU])
    rw [hU] at hgrow
    have hind := hindependent i S2 (by
      intro j hj
      exact (Finset.mem_filter.mp hj).2)
    have hind' : ((((av A S2).filter (fun w => w ∈ A i)).card : ℕ) : ℝ)
        * (Fintype.card Omega : ℝ) = ((av A S2).card : ℝ) * ((A i).card : ℝ) := by
      have h := hind
      simp only [av] at *
      field_simp at h
      first
        | linarith
        | exact h
        | (convert h using 3 <;> (congr 1 <;> (try ext w) <;> simp))
    have hpi := hprob i
    rw [div_le_iff₀ hN] at hpi
    have hsub : ((av A S).filter (fun w => w ∈ A i)).card
        ≤ ((av A S2).filter (fun w => w ∈ A i)).card := by
      apply Finset.card_le_card
      apply Finset.filter_subset_filter
      apply av_mono
      exact Finset.filter_subset _ _
    have hsub' : ((((av A S).filter (fun w => w ∈ A i)).card : ℕ) : ℝ)
        ≤ ((((av A S2).filter (fun w => w ∈ A i)).card : ℕ) : ℝ) := by exact_mod_cast hsub
    have hS1card : S1.card ≤ (Finset.univ.filter (fun j => dep i j)).card := by
      apply Finset.card_le_card
      exact Finset.filter_subset_filter _ (Finset.subset_univ S)
    have hpow : (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card ≤ (1 - x) ^ S1.card :=
      pow_le_pow_of_le_one (le_of_lt h1x) (by linarith) hS1card
    -- |A_i ∩ av S2| ≤ |av S2| * x * (1-x)^{|S1|}
    have hav2 : (0 : ℝ) ≤ ((av A S2).card : ℝ) := by positivity
    have hstep : ((((av A S2).filter (fun w => w ∈ A i)).card : ℕ) : ℝ)
        ≤ ((av A S2).card : ℝ) * (x * (1 - x) ^ S1.card) := by
      have h3 : ((av A S2).card : ℝ) * ((A i).card : ℝ)
          ≤ ((av A S2).card : ℝ) * (x * (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card
              * (Fintype.card Omega : ℝ)) := mul_le_mul_of_nonneg_left hpi hav2
      have h4 : ((((av A S2).filter (fun w => w ∈ A i)).card : ℕ) : ℝ)
          ≤ ((av A S2).card : ℝ) * (x * (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card) := by
        have h5 : ((((av A S2).filter (fun w => w ∈ A i)).card : ℕ) : ℝ) * (Fintype.card Omega : ℝ)
            ≤ (((av A S2).card : ℝ) * (x * (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card))
              * (Fintype.card Omega : ℝ) := by
          rw [hind']; linarith
        exact le_of_mul_le_mul_right h5 hN
      calc _ ≤ _ := h4
        _ ≤ ((av A S2).card : ℝ) * (x * (1 - x) ^ S1.card) := by
          apply mul_le_mul_of_nonneg_left _ hav2
          exact mul_le_mul_of_nonneg_left hpow hx0
    calc ((((av A S).filter (fun w => w ∈ A i)).card : ℕ) : ℝ)
        ≤ ((av A S2).card : ℝ) * (x * (1 - x) ^ S1.card) := le_trans hsub' hstep
      _ = x * ((1 - x) ^ S1.card * ((av A S2).card : ℝ)) := by ring
      _ ≤ x * ((av A S).card : ℝ) := mul_le_mul_of_nonneg_left hgrow hx0
  have hall : ∀ n : ℕ, ∀ S : Finset I, S.card < n → CB A x S := by
    intro n
    induction n with
    | zero => intro S h; omega
    | succ n ih =>
      intro S hS
      apply key
      intro V hV
      exact ih V (by omega)
  have hposS : ∀ S : Finset I, 0 < (av A S).card := by
    intro S
    have hg := grow A x (le_of_lt hx1) S.card (fun V hV => hall S.card V hV) S ∅
      (Finset.disjoint_empty_right S) (by simp)
    rw [Finset.union_empty, av_empty, Finset.card_univ] at hg
    have hpos : (0 : ℝ) < (1 - x) ^ S.card * (Fintype.card Omega : ℝ) := by positivity
    have h' : (0 : ℝ) < ((av A S).card : ℝ) := lt_of_lt_of_le hpos hg
    have h'' : 0 < (av A S).card := by exact_mod_cast h'
    exact h''
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (hposS Finset.univ)
  refine ⟨w, fun i => ?_⟩
  simp only [av, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  exact hw i (by simp)

theorem solution
    (Omega I : Type*) [Fintype Omega] [Nonempty Omega] [DecidableEq Omega]
    [Fintype I] [DecidableEq I]
    (A : I -> Finset Omega) (dep : I -> I -> Prop) [DecidableRel dep]
    (x : Real) (hx0 : 0 <= x) (hx1 : x < 1)
    (hprob : forall i,
      ((A i).card : Real) / (Fintype.card Omega : Real) <=
        x * (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card)
    (hindependent : forall (i : I) (S : Finset I),
      (forall j, Membership.mem S j -> Not (dep i j)) ->
      ((Finset.filter (fun w => Membership.mem (A i) w)
          (Finset.univ.filter (fun w => forall j, Membership.mem S j ->
            Not (Membership.mem (A j) w)))).card : Real) /
          (Fintype.card Omega : Real) =
        (((Finset.univ.filter (fun w => forall j, Membership.mem S j ->
            Not (Membership.mem (A j) w))).card : Real) /
            (Fintype.card Omega : Real)) *
          ((A i).card : Real) / (Fintype.card Omega : Real)) :
    Exists fun w : Omega => forall i, Not (Membership.mem (A i) w) := by
  exact P2M7ce7e904.crit Omega I A dep x hx0 hx1 hprob hindependent
