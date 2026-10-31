-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_ubv_HJB_candidate_dominates_initial_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:04:48.102036+00:00
-- url     : https://prove2.me/submissions/e614a20b-7d34-48df-a803-60f8c923dfd8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- With the corrected zero boundary, the genuine UBV HJB candidate
dominates the current reserve everywhere up to any nonnegative cap. -/
theorem solution
    (C : ℝ≥0∞) (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x)
    (hxc : ENNReal.ofReal x ≤ C) :
    x ≤ w x := by
  have hsec := avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
    C w hw_cont hw_smooth hw_grad 0 x (le_refl 0) hx hxc
  linarith
