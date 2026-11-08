-- Prove2me | solution 2 for AvramDividend.Classical.avram_bv_strict12_original_contact_correction_crossing_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:52:29.877142+00:00
-- url     : https://prove2.me/submissions/f6e1d759-1ef3-4fd5-8760-cbde1727ae81

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal
noncomputable section

/-- The residual discarded when clipping a physical cell at ruin is supported
    precisely on the cells whose right endpoint lies strictly after ruin. -/
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
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h : E i
  · by_cases hcross : τ < u (i + 1)
    · simp [h, hcross, min_eq_right (le_of_lt hcross)]
    · have hle : u (i + 1) ≤ τ := le_of_not_gt hcross
      simp [h, hcross, min_eq_left hle]
  · simp [h]
