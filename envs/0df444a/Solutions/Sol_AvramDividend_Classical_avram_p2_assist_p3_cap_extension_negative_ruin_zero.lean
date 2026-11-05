-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_assist_p3_cap_extension_negative_ruin_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:05:12.095077+00:00
-- url     : https://prove2.me/submissions/074c1141-9594-4a0e-8553-3083f7e8ca46

import Mathlib.Data.ENNReal.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal
noncomputable section

/-- The actual source cap extension preserves ruin-side vanishing. -/
theorem solution
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0) :
    ∀ z : ℝ, z < 0 → V z = 0 := by
  intro z hz
  by_cases hC : C = ⊤
  · rw [hVtop hC z]
    exact hw_neg z hz
  · have hzcap : z ≤ C.toReal :=
      le_trans (le_of_lt hz) ENNReal.toReal_nonneg
    rw [hVfinite hC z, if_pos hzcap]
    exact hw_neg z hz
