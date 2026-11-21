-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_active_postmark_upper_strip_compensator_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:15:52.767736+00:00
-- url     : https://prove2.me/submissions/e4f26633-8413-4039-b932-baf2171289ee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_linear_crossing_secant
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_caplinear_upperband_mark_compensator_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_caplinear_downcross_mark_remainder_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y z : ℝ) (hy : C.toReal < y) (hz : 0 ≤ y + z) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    V (y + z) - V y - deriv V y * z ≤ 0 := by
  dsimp only
  by_cases hcross : y + z ≤ C.toReal
  · have hsec :=
      avram_p3_bv_finite_cap_linear_crossing_secant
        C hC hFinite w hw_cont hw_smooth hw_grad
        (y + z) C.toReal hz hcross le_rfl
    have hslope : w (y + z) - w C.toReal ≤ y + z - C.toReal := by
      linarith
    exact avram_mix_inf20_caplinear_downcross_mark_remainder_nonpos
      w C.toReal y z hy hcross hslope
  · exact le_of_eq
      (avram_mix_inf20_original_caplinear_upperband_mark_compensator_zero
        w C.toReal y z hy (lt_of_not_ge hcross))
