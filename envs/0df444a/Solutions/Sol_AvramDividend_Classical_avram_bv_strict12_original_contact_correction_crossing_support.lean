-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict12_original_contact_correction_crossing_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:51:46.923884+00:00
-- url     : https://prove2.me/submissions/cf6b5477-0f5f-4b98-9bdb-80e3107d735c

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal
noncomputable section

theorem solution
    (n : ℕ) (u : ℕ → ℝ≥0) (τ : ℝ≥0) (R : ℝ≥0 → ℝ)
    (W : ℕ → ℝ) (E : ℕ → Prop) :
    (∑ i ∈ Finset.range n,
      if E i then
        W i * (R (min (u (i + 1)) τ) - R (u (i + 1))) else 0) =
    (∑ i ∈ Finset.range n,
      if E i ∧ τ < u (i + 1) then
        W i * (R τ - R (u (i + 1))) else 0) := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hE : E i
  · by_cases hcross : τ < u (i + 1)
    · simp [hE, hcross, min_eq_right (le_of_lt hcross)]
    · have hle : u (i + 1) ≤ τ := le_of_not_gt hcross
      simp [hE, hcross, min_eq_left hle]
  · simp [hE]
