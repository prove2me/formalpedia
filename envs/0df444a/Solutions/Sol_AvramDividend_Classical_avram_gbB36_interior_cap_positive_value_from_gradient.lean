-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB36_interior_cap_positive_value_from_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:27:27.089248+00:00
-- url     : https://prove2.me/submissions/c60604d8-7862-48fa-b05a-11e6bc0e4a52

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b ≤ C) :
    0 ≤ w b := by
  have hs := avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
    C w hw_cont hw_smooth hw_grad (0 : ℝ) b le_rfl hb hbC
  linarith
