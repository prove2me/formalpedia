-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_scale_ordinary_deriv_ne_positive_right_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:09:34.833452+00:00
-- url     : https://prove2.me/submissions/f642343e-4065-4ef6-a0da-ed0e20a546d2

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_ordinary_deriv_zero_at_origin
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

/-- Separate the ordinary derivative at zero from the one-sided Gaussian slope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    deriv W 0 ≠ 2 / X.σ ^ 2 := by
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ
  rw [scaleFunction_ordinary_deriv_zero_at_origin X q W hW hzero]
  have hpos : 0 < (2 : ℝ) / X.σ ^ 2 := by positivity
  exact ne_of_lt hpos
