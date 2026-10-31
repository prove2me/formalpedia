-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_repaired_boundary_nonneg_all_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:04:42.473696+00:00
-- url     : https://prove2.me/submissions/d506fd85-a397-4a1b-ac7d-0ab12941fe85

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Correct boundary nonnegativity holds at every nonnegative reserve
within any cap, including the zero-cap endpoint. -/
theorem solution
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (y : ℝ) (hy : 0 ≤ y)
    (hcap : ENNReal.ofReal y ≤ C) :
    0 ≤ w y := by
  by_cases hC : 0 < C
  · have hsec := avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad 0 y (le_refl _) hy hcap
    linarith
  · have hC0 : C = 0 := bot_unique (le_of_not_gt hC)
    have hz : ENNReal.ofReal y = 0 := by
      rw [hC0] at hcap
      exact bot_unique hcap
    have hy0 : y = 0 :=
      le_antisymm (ENNReal.ofReal_eq_zero.mp hz) hy
    simpa [hy0] using hw0
