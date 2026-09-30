-- Prove2me | solution 1 for ComplementFreeCA.ValueQuery.case_one_all_to_one
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:43:06.61126+00:00
-- url     : https://prove2.me/submissions/78ae582a-8bf2-43b1-8ce6-3d92a35f6086

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Definitions.Def_ComplementFreeCA_ValueQuery_Basic
open Finset ComplementFreeCA.ValueQuery

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
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
