-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_affine_singular_global_positive_reserve_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:49:17.043895+00:00
-- url     : https://prove2.me/submissions/b6d385a0-e190-449e-9d33-2071f0e557be

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_original_generator_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_large_reserve_generator_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Combine the two source-exact compensated-generator integrability regimes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (x : ℝ) (hx : 0 < x) :
    X.GeneratorIntegrable
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x := by
  by_cases hsmall : x < 1
  · exact avram_a19_affine_singular_original_generator_integrable X hν x hx hsmall
  · exact avram_a19_affine_singular_large_reserve_generator_integrable
      X hν x (le_of_not_gt hsmall)
