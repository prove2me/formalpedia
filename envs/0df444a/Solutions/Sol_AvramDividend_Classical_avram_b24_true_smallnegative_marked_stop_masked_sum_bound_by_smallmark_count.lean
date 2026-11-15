-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_true_smallnegative_marked_stop_masked_sum_bound_by_smallmark_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:23:01.09775+00:00
-- url     : https://prove2.me/submissions/d4234492-0d94-4efc-8147-aab631edda40

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {α : Type*} (S : Finset α) (z : α → ℝ) (mask : α → Bool)
    (T t : ℝ≥0) (ht : t ≤ T) (d : ℝ) :
    ‖(∑ i ∈ S, if mask i then
        (if -1 < z i ∧ z i < 0 then z i else 0) else 0) -
      (t : ℝ) * d‖ ≤
      ((S.filter (fun i => -1 < z i ∧ z i < 0)).card : ℝ) +
        (T : ℝ) * ‖d‖ := by
  classical
  have htReal : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
  have htNonneg : (0 : ℝ) ≤ (t : ℝ) := NNReal.coe_nonneg t
  have hBound (i : α) :
      ‖if mask i then (if -1 < z i ∧ z i < 0 then z i else 0) else 0‖ ≤
        if -1 < z i ∧ z i < 0 then (1 : ℝ) else 0 := by
    by_cases hSmall : -1 < z i ∧ z i < 0
    · by_cases hMask : mask i
      · simp only [if_pos hMask, if_pos hSmall]
        rw [Real.norm_eq_abs, abs_of_nonpos (le_of_lt hSmall.2)]
        linarith [hSmall.1]
      · simp [hMask, hSmall]
    · simp [hSmall]
  have hSum :
      ‖∑ i ∈ S, if mask i then
        (if -1 < z i ∧ z i < 0 then z i else 0) else 0‖ ≤
        ((S.filter (fun i => -1 < z i ∧ z i < 0)).card : ℝ) := by
    calc
      ‖∑ i ∈ S, if mask i then
        (if -1 < z i ∧ z i < 0 then z i else 0) else 0‖ ≤
        ∑ i ∈ S,
          ‖if mask i then
            (if -1 < z i ∧ z i < 0 then z i else 0) else 0‖ :=
        norm_sum_le S _
      _ ≤ ∑ i ∈ S, if -1 < z i ∧ z i < 0 then (1 : ℝ) else 0 :=
        Finset.sum_le_sum (fun i hi => hBound i)
      _ = ((S.filter (fun i => -1 < z i ∧ z i < 0)).card : ℝ) := by
        simp
  have hTnorm : ‖(t : ℝ)‖ = (t : ℝ) :=
    Real.norm_eq_abs (t : ℝ) ▸ abs_of_nonneg htNonneg
  have hDrift : ‖(t : ℝ) * d‖ ≤ (T : ℝ) * ‖d‖ := by
    rw [norm_mul, hTnorm]
    exact mul_le_mul_of_nonneg_right htReal (norm_nonneg d)
  calc
    ‖(∑ i ∈ S, if mask i then
      (if -1 < z i ∧ z i < 0 then z i else 0) else 0) -
      (t : ℝ) * d‖ ≤
      ‖∑ i ∈ S, if mask i then
        (if -1 < z i ∧ z i < 0 then z i else 0) else 0‖ +
      ‖(t : ℝ) * d‖ := norm_sub_le _ _
    _ ≤ ((S.filter (fun i => -1 < z i ∧ z i < 0)).card : ℝ) +
        (T : ℝ) * ‖d‖ :=
      add_le_add hSum hDrift
