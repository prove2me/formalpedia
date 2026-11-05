-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_finite_cap_linear_crossing_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:14:51.573882+00:00
-- url     : https://prove2.me/submissions/47f61de2-084b-43f3-b2c1-851952ae2815

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The slope-one continuation gives the correct dividend secant across
a finite cap using only the canonical BV interior C1 gradient bound. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (a b : ℝ) (ha : 0 ≤ a) (haC : a ≤ C.toReal)
    (hCb : C.toReal ≤ b) :
    b - a ≤ (w C.toReal + (b - C.toReal)) - w a := by
  have hReal : ENNReal.ofReal C.toReal ≤ C :=
    le_of_eq (ENNReal.ofReal_toReal hfinite)
  have hsec := avram_wave3_03_bv_full_cap_gradient_secant
    C hC w hw_cont hw_smooth hw_grad
      a C.toReal ha haC hReal
  linarith only [hsec]
