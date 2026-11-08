-- Prove2me | solution 2 for AvramDividend.Classical.avram_ubv_top9_original_topcap_w_ge_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:59:00.875202+00:00
-- url     : https://prove2.me/submissions/8a9b3787-124b-4286-b4c8-19ce5eb98d2d

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The closed-cap gradient envelope includes the infinite cap. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y : ℝ) (hy : 0 ≤ y) :
    y ≤ w y := by
  have hC : (0 : ℝ≥0∞) < C := by simp [hTop]
  have hC1 : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} :=
    hw_smooth.of_le (by norm_num)
  have hycap : ENNReal.ofReal y ≤ C := by simp [hTop]
  have h := avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
    C hC w hw_cont hC1 hw_grad y hy hycap y
      (by exact ⟨hy, le_refl y⟩)
  linarith only [h, hw0]
