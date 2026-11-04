-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:53:34.19729+00:00
-- url     : https://prove2.me/submissions/d7c83f4f-8e49-4711-8eca-e02d8a8ca8f5

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The exact original C² interior and slope-one bound imply w≥0 at every capped nonnegative state, even for an infinite cap. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwSmooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → 0 ≤ w y := by
  intro y hy0 hyCap
  have hSec :=
    avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
      C w hwCont hwSmooth hwGrad 0 y (le_refl _) hy0 hyCap
  linarith
