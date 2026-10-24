-- Prove2me | solution 1 for AvramDividend.Classical.generatorIntegrand_large_negative_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:17:14.807345+00:00
-- url     : https://prove2.me/submissions/5575d8d8-8a82-410c-9a65-2713f373c7a8

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- On large negative jumps the compensated kernel is the full value increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    IntegrableOn (fun y : ℝ => w (x + y) - w x) (Iic (-1 : ℝ)) X.ν := by
  have hsub : Iic (-1 : ℝ) ⊆ Iio 0 := by
    intro y hy
    change y ≤ (-1 : ℝ) at hy
    change y < (0 : ℝ)
    exact lt_of_le_of_lt hy (by norm_num)
  have hLarge := hGen.mono_set hsub
  refine hLarge.congr_fun ?_ measurableSet_Iic
  intro y hy
  change SpectrallyNegativeLevy.generatorIntegrand w x y =
    w (x + y) - w x
  exact generatorIntegrand_large_negative w x y hy
