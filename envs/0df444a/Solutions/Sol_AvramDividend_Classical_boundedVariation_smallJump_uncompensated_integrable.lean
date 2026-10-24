-- Prove2me | solution 1 for AvramDividend.Classical.boundedVariation_smallJump_uncompensated_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:15:06.268297+00:00
-- url     : https://prove2.me/submissions/7994446d-585c-4571-9e89-5d1c0990c147

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_small_negative
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_kernel_plus_deriv_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Restore the uncompensated small-jump candidate increment integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    IntegrableOn (fun y : ℝ => w (x + y) - w x) (Ioo (-1 : ℝ) 0) X.ν := by
  have hSum :=
    boundedVariation_smallJump_kernel_plus_deriv_integrable X hBV w x hGen
  refine hSum.congr_fun ?_ measurableSet_Ioo
  intro y hy
  change SpectrallyNegativeLevy.generatorIntegrand w x y +
    deriv w x * y = w (x + y) - w x
  rw [generatorIntegrand_small_negative w x y hy]
  ring
