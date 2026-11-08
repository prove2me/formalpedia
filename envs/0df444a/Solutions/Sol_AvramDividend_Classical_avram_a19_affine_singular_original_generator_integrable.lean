-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_affine_singular_original_generator_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:33:08.052742+00:00
-- url     : https://prove2.me/submissions/5d1b03fa-6b6d-4224-a595-1212a799342c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen15_affine_singular_generator_jump_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The computed singular-density integral gives the original generator integrability predicate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (x : ℝ) (hx : 0 < x) (hcap : x < 1) :
    X.GeneratorIntegrable
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x := by
  change IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand
    (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x) (Iio 0) X.ν
  rw [hν]
  exact (avram_gen15_affine_singular_generator_jump_integrable x hx hcap).integrableOn
