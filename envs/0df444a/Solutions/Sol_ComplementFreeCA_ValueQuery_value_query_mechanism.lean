-- Prove2me | solution 1 for ComplementFreeCA.ValueQuery.value_query_mechanism
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:45:53.017281+00:00
-- url     : https://prove2.me/submissions/2e476c19-8f4f-47f2-8a0c-c07b537696cb

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Definitions.Def_ComplementFreeCA_ValueQuery_Basic
open Finset ComplementFreeCA.ValueQuery


private theorem vcg_truthful {n m : ℕ}
    (D : (Finset (Fin m) → ℝ) → Prop) (R : Set (Fin n → Finset (Fin m)))
    (f : (Fin n → Finset (Fin m) → ℝ) → Fin n → Finset (Fin m))
    (hf : IsMaximalInRange D R f) : IncentiveCompatibleOn D f := by
  classical
  intro v hv i v' hv'
  have hu : ∀ k, D (Function.update v i v' k) := by
    intro k
    by_cases hki : k = i
    · subst k
      simpa using hv'
    · simpa [Function.update_of_ne hki] using hv k
  have h := (hf v hv).2 _ (hf _ hu).1
  have heq : ∀ A : Fin n → Finset (Fin m),
      v i (A i) + ∑ k ∈ univ.erase i, Function.update v i v' k (A k) = welfare v A := by
    intro A
    rw [welfare, ← add_sum_erase univ (fun k => v k (A k)) (mem_univ i)]
    congr 1
    apply sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (mem_erase.mp hk).1]
  unfold vcgUtility vcgPayment
  rw [heq]
  unfold welfare at h ⊢
  rw [← add_sum_erase univ (fun k => v k (f v k)) (mem_univ i)] at h
  exact h


private theorem matching_alloc_good {n m : ℕ} (μ : Fin m → Option (Fin n)) (hμ : IsMatching μ) :
    IsAllocation (matchingAlloc μ) ∧ ∀ i, (matchingAlloc μ i).card ≤ 1 := by
  refine ⟨?_, ?_⟩
  · intro i i' hne
    apply disjoint_left.mpr
    intro j hj hj'
    simp only [matchingAlloc, mem_filter, mem_univ, true_and] at hj hj'
    exact hne (Option.some.inj (hj.symm.trans hj'))
  · intro i
    apply card_le_one.mpr
    intro j hj j' hj'
    exact hμ j j' i (mem_filter.mp hj).2 (mem_filter.mp hj').2

private theorem matching_welfare {n m : ℕ} (b : Fin n → Finset (Fin m) → ℝ)
    (hb : ∀ i, IsNormalized (b i)) (μ : Fin m → Option (Fin n)) (hμ : IsMatching μ) :
    welfare b (matchingAlloc μ) = matchingWeight b μ := by
  classical
  have hone := (matching_alloc_good μ hμ).2
  have hsingle : ∀ i, b i (matchingAlloc μ i) = ∑ j ∈ matchingAlloc μ i, b i {j} := by
    intro i
    rcases eq_empty_or_nonempty (matchingAlloc μ i) with h | ⟨j, hj⟩
    · simp [h, show b i ∅ = 0 from hb i]
    · have he : matchingAlloc μ i = {j} := by
        ext k
        simp only [mem_singleton]
        constructor
        · intro hk
          exact card_le_one.mp (hone i) k hk j hj
        · intro hk
          subst k
          exact hj
      simp [he]
  unfold welfare
  simp_rw [hsingle]
  simp only [matchingAlloc, sum_filter]
  rw [sum_comm]
  unfold matchingWeight
  apply sum_congr rfl
  intro j hj
  cases h : μ j with
  | none => simp [h]
  | some i => simp [h, eq_comm]

private theorem represent_singletons {n m : ℕ} (A : Fin n → Finset (Fin m))
    (hA : IsAllocation A) (hone : ∀ i, (A i).card ≤ 1) :
    ∃ μ : Fin m → Option (Fin n), IsMatching μ ∧ matchingAlloc μ = A := by
  classical
  let μ : Fin m → Option (Fin n) := fun j => if h : ∃ i, j ∈ A i then some h.choose else none
  have he : ∀ j i, μ j = some i ↔ j ∈ A i := by
    intro j i
    dsimp [μ]
    split_ifs with h
    · constructor
      · intro hi
        rw [← Option.some.inj hi]
        exact h.choose_spec
      · intro hj
        congr 1
        by_contra hne
        exact disjoint_left.mp (hA h.choose i hne) h.choose_spec hj
    · simp only [reduceCtorEq, false_iff]
      exact fun hj => h ⟨i,hj⟩
  refine ⟨μ, ?_, ?_⟩
  · intro j j' i hj hj'
    exact card_le_one.mp (hone i) j ((he j i).mp hj) j' ((he j' i).mp hj')
  · funext i
    ext j
    simp [matchingAlloc, he]

private theorem alg_maximal {n m : ℕ}
    (mat : (Fin n → Finset (Fin m) → ℝ) → Fin m → Option (Fin n))
    (top : (Fin n → Finset (Fin m) → ℝ) → Fin n)
    (hmat : IsMaxWeightMatchingRule mat) (htop : IsTopBidderRule top) :
    IsMaximalInRange IsNormalized ValueQueryRange (alg mat top) := by
  classical
  intro b hb
  have hall : ∀ i, welfare b (allToOne i) = b i univ := by
    intro i
    simp [welfare, allToOne, apply_ite, show ∀ k, b k ∅ = 0 from hb]
  have hmatch := matching_welfare b hb (mat b) (hmat b).1
  have hw : welfare b (alg mat top b) = max (matchingWeight b (mat b)) (b (top b) univ) := by
    unfold alg
    split_ifs with h
    · rw [hall, max_eq_right h.le]
    · rw [hmatch, max_eq_left (le_of_not_gt h)]
  refine ⟨?_, ?_⟩
  · unfold alg
    split_ifs
    · exact Or.inl ⟨top b, rfl⟩
    · exact Or.inr (matching_alloc_good (mat b) (hmat b).1)
  · intro A hA
    rw [hw]
    rcases hA with ⟨i, rfl⟩ | ⟨hA, hone⟩
    · rw [hall]
      exact (htop b i).trans (le_max_right _ _)
    · obtain ⟨μ,hμ,hμA⟩ := represent_singletons A hA hone
      rw [← hμA, matching_welfare b hb μ hμ]
      exact ((hmat b).2 μ hμ).trans (le_max_left _ _)


private theorem case_one {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsCFValuation (v i)) (O : Fin n → Finset (Fin m)) (hO : IsAllocation O)
    (hcase : ∑ i ∈ univ.filter (fun i => ((O i).card : ℝ) < Real.sqrt m), v i (O i) ≤
      ∑ i ∈ univ.filter (fun i => Real.sqrt m ≤ ((O i).card : ℝ)), v i (O i))
    (i₀ : Fin n) (hi₀ : ∀ i, v i univ ≤ v i₀ univ) :
    welfare v O ≤ 2 * Real.sqrt m * v i₀ univ := by
  classical
  have hv0 : ∀ i S, 0 ≤ v i S := by
    intro i S
    have h := (hv i).2.1 ∅ S (empty_subset S)
    simpa only [(show v i ∅ = 0 from (hv i).1)] using h
  have htop : ∀ i, v i (O i) ≤ v i₀ univ := by
    intro i
    exact ((hv i).2.1 _ _ (subset_univ _)).trans (hi₀ i)
  have hcard : ∑ i, (O i).card ≤ m := by
    have he : (univ.biUnion O).card = ∑ i, (O i).card := card_biUnion (by
      intro i hi i' hi' hne
      exact hO i i' hne)
    rw [← he]
    simpa using card_le_card (subset_univ (univ.biUnion O))
  have hcardR : (∑ i, ((O i).card : ℝ)) ≤ m := by exact_mod_cast hcard
  by_cases hm : m = 0
  · subst m
    have he : ∀ i, O i = ∅ := by intro i; exact Finset.eq_empty_of_isEmpty _
    simp [welfare, he, show ∀ i, v i ∅ = 0 from fun i => (hv i).1]
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hm)
  let B := univ.filter (fun i => Real.sqrt m ≤ ((O i).card : ℝ))
  have hB : (B.card : ℝ) ≤ Real.sqrt m := by
    have h1 : (B.card:ℝ)*Real.sqrt m ≤ ∑ i ∈ B, ((O i).card:ℝ) := by
      calc
        _ = ∑ i ∈ B, Real.sqrt m := by simp
        _ ≤ _ := sum_le_sum (fun i hi => (mem_filter.mp hi).2)
    have h2 : (∑ i ∈ B, ((O i).card:ℝ)) ≤ ∑ i, ((O i).card:ℝ) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i hi hnot => Nat.cast_nonneg _)
    have hsq := Real.sq_sqrt (show (0:ℝ) ≤ m by positivity)
    nlinarith
  have hval : ∑ i ∈ B, v i (O i) ≤ Real.sqrt m * v i₀ univ := by
    calc
      ∑ i ∈ B, v i (O i) ≤ ∑ i ∈ B, v i₀ univ := sum_le_sum (fun i hi => htop i)
      _ = (B.card:ℝ) * v i₀ univ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hB (hv0 _ _)
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset (Fin n))
    (fun i => ((O i).card:ℝ) < Real.sqrt m) (fun i => v i (O i))
  simp only [not_lt] at hsplit
  unfold welfare
  dsimp [B] at hval
  linarith


private theorem singleton_bound {m : ℕ} (v : Finset (Fin m) → ℝ) (hv : IsCFValuation v)
    (T : Finset (Fin m)) (c : Fin m) (hmax : ∀ j ∈ T, v {j} ≤ v {c}) :
    v T ≤ (T.card : ℝ) * v {c} := by
  have hsum : ∀ S : Finset (Fin m), v S ≤ ∑ j ∈ S, v {j} := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa only [sum_empty] using le_of_eq hv.1
    | @insert a S ha ih =>
      have h := (hv.2.2 {a} S).trans (add_le_add le_rfl ih)
      simpa only [singleton_union, sum_insert ha] using h
  exact (hsum T).trans (by simpa using sum_le_sum hmax)

private theorem case_two {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsCFValuation (v i)) (O : Fin n → Finset (Fin m)) (hO : IsAllocation O)
    (hcase : ∑ i ∈ univ.filter (fun i => Real.sqrt m ≤ ((O i).card : ℝ)), v i (O i) <
      ∑ i ∈ univ.filter (fun i => ((O i).card : ℝ) < Real.sqrt m), v i (O i)) :
    ∃ A : Fin n → Finset (Fin m), IsAllocation A ∧ (∀ i, (A i).card ≤ 1) ∧
      welfare v O ≤ 2 * Real.sqrt m * welfare v A := by
  classical
  have hv0 : ∀ i S, 0 ≤ v i S := by
    intro i S
    have h := (hv i).2.1 ∅ S (empty_subset S)
    simpa only [(show v i ∅ = 0 from (hv i).1)] using h
  have hex : ∀ i, ∃ A : Finset (Fin m), A ⊆ O i ∧ A.card ≤ 1 ∧ v i (O i) ≤ ((O i).card:ℝ)*v i A := by
    intro i
    rcases eq_empty_or_nonempty (O i) with he | hn
    · refine ⟨∅, empty_subset _, by simp, ?_⟩
      simp [he, show v i ∅ = 0 from (hv i).1]
    · obtain ⟨c,hc,hmax⟩ := exists_max_image (O i) (fun j => v i {j}) hn
      exact ⟨{c}, singleton_subset_iff.mpr hc, by simp, singleton_bound _ (hv i) _ c hmax⟩
  choose A hsub hcard hval using hex
  refine ⟨A, ?_, hcard, ?_⟩
  · intro i i' hne
    exact (hO i i' hne).mono (hsub i) (hsub i')
  · have hsmall : ∑ i ∈ univ.filter (fun i => ((O i).card:ℝ) < Real.sqrt m), v i (O i) ≤
        Real.sqrt m * welfare v A := by
      rw [sum_filter, welfare, mul_sum]
      apply sum_le_sum
      intro i hi
      split_ifs with h
      · exact (hval i).trans (mul_le_mul_of_nonneg_right h.le (hv0 i _))
      · exact mul_nonneg (Real.sqrt_nonneg _) (hv0 i _)
    have hsplit := sum_filter_add_sum_filter_not (univ : Finset (Fin n))
      (fun i => ((O i).card:ℝ) < Real.sqrt m) (fun i => v i (O i))
    simp only [not_lt] at hsplit
    unfold welfare at *
    nlinarith
theorem solution {n m : ℕ}
    (mat : (Fin n → Finset (Fin m) → ℝ) → Fin m → Option (Fin n))
    (top : (Fin n → Finset (Fin m) → ℝ) → Fin n)
    (hmat : IsMaxWeightMatchingRule mat) (htop : IsTopBidderRule top) :
    (∀ v : Fin n → Finset (Fin m) → ℝ, (∀ i, IsCFValuation (v i)) →
      ∀ O : Fin n → Finset (Fin m), IsAllocation O →
        welfare v O ≤ 2 * Real.sqrt m * welfare v (alg mat top v)) ∧
    IncentiveCompatibleOn IsCFValuation (alg mat top) := by
  classical
  have hmax := alg_maximal mat top hmat htop
  constructor
  · intro v hv O hO
    have hvnorm : ∀ i, IsNormalized (v i) := fun i => (hv i).1
    have hscale : 0 ≤ 2 * Real.sqrt m := by positivity
    by_cases hc : (∑ i ∈ univ.filter (fun i => ((O i).card : ℝ) < Real.sqrt m), v i (O i)) ≤
        ∑ i ∈ univ.filter (fun i => Real.sqrt m ≤ ((O i).card : ℝ)), v i (O i)
    · have hcase := case_one v hv O hO hc (top v) (htop v)
      have hm := (hmax v hvnorm).2 (allToOne (top v)) (Or.inl ⟨top v, rfl⟩)
      have he : welfare v (allToOne (top v)) = v (top v) univ := by
        simp [welfare, allToOne, apply_ite, show ∀ i, v i ∅ = 0 from hvnorm]
      rw [he] at hm
      exact hcase.trans (mul_le_mul_of_nonneg_left hm hscale)
    · obtain ⟨A,hA,hcard,hval⟩ := case_two v hv O hO (lt_of_not_ge hc)
      have hm := (hmax v hvnorm).2 A (Or.inr ⟨hA,hcard⟩)
      exact hval.trans (mul_le_mul_of_nonneg_left hm hscale)
  · apply vcg_truthful IsCFValuation ValueQueryRange (alg mat top)
    intro v hv
    exact hmax v (fun i => (hv i).1)
