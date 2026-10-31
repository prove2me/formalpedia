-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:41:43.455664+00:00
-- url     : https://prove2.me/submissions/02ff05c7-b2e6-421d-bc66-bac65b9063e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The UBV C² gradient HJB premise controls every downward dividend
value drop on the closed cap, including the degenerate zero cap. -/
theorem solution
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : ENNReal.ofReal b ≤ C) :
    b - a ≤ w b - w a := by
  by_cases hC : 0 < C
  · exact avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont (hw_smooth.of_le (by norm_num))
      hw_grad a b ha hab hb
  · have hC0 : C = 0 := bot_unique (le_of_not_gt hC)
    have hB0 : b = 0 := by
      have hb0 : ENNReal.ofReal b = 0 := by
        rw [hC0] at hb
        exact bot_unique hb
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp hb0)
        (le_trans ha hab)
    have hA0 : a = 0 := le_antisymm (by simpa [hB0] using hab) ha
    simp [hA0, hB0]
