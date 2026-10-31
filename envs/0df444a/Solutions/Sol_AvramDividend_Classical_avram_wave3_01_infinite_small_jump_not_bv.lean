-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_infinite_small_jump_not_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:42:56.004007+00:00
-- url     : https://prove2.me/submissions/33c87d2d-b571-4dd5-bda0-dfa7fe622775

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Infinite first variation in the small negative jumps excludes the
bounded-variation Lévy branch by the proved source integrability theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ¬ X.BoundedVariation := by
  intro hBV
  have hI : IntegrableOn (fun y : ℝ => y)
      (Ioo (-1 : ℝ) 0) X.ν :=
    boundedVariation_smallJump_integrable X hBV
  have hfinite := hI.hasFiniteIntegral
  have hlt :
      (∫⁻ y in Ioo (-1 : ℝ) 0,
        ENNReal.ofReal |y| ∂X.ν) < ⊤ := by
    simpa only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs] using hfinite
  exact (ne_of_lt hlt) hvar
