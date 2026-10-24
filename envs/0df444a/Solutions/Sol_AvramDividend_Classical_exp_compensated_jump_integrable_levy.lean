-- Prove2me | solution 1 for AvramDividend.Classical.exp_compensated_jump_integrable_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:33:42.037361+00:00
-- url     : https://prove2.me/submissions/55b3ec13-cbc9-459d-9c4f-29a30843def6

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_compensated_jump_integrable
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The full compensated exponential is the canonical integrable jump kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    IntegrableOn
      (fun y : ℝ => Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)
      (Iio 0) X.ν := by
  exact compensated_jump_integrable X θ hθ
