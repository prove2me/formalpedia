-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_slope_one_supporting_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:46:55.803003+00:00
-- url     : https://prove2.me/submissions/a3ac523f-42b4-4fab-8a42-89b0dc96c38a

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
The cap-linear extension is bounded above on nonnegative reserves by the
slope-one supporting affine line through the cap. This does not use a left
derivative or any C2 property at the cap itself.
-/

/-- The cap affine line majorizes the slope-one continuation globally. -/
theorem solution
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (y : ℝ) (hy : 0 ≤ y) :
    (if y ≤ c then w y else w c + (y - c)) ≤ w c + (y - c) := by
  by_cases hyc : y ≤ c
  · simp only [if_pos hyc]
    have hSec :=
      avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
        (ENNReal.ofReal c) w hw_cont hw_smooth hw_grad
        y c hy hyc le_rfl
    linarith
  · simp [hyc]
