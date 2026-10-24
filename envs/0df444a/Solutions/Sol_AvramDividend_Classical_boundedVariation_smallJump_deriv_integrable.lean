-- Prove2me | solution 1 for AvramDividend.Classical.boundedVariation_smallJump_deriv_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:56:08.219499+00:00
-- url     : https://prove2.me/submissions/c0c6b918-1bc7-48c9-ab3e-116500c8a712

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_integrable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The derivative-weighted Lévy small-jump compensator is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) :
    IntegrableOn (fun y : ℝ => deriv w x * y) (Ioo (-1 : ℝ) 0) X.ν := by
  exact (boundedVariation_smallJump_integrable X hBV).const_mul (deriv w x)
