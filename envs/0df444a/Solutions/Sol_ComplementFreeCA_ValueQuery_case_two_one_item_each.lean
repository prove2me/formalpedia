-- Prove2me | solution 1 for ComplementFreeCA.ValueQuery.case_two_one_item_each
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:44:29.930744+00:00
-- url     : https://prove2.me/submissions/e29cb5d1-4c60-495e-8738-de39fe4b629d

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Definitions.Def_ComplementFreeCA_ValueQuery_Basic
open Finset ComplementFreeCA.ValueQuery

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

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
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
