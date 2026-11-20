-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_Levy_Dirac_negative2_generator_mark_integral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:52:56.000868+00:00
-- url     : https://prove2.me/submissions/a4176d1a-2b23-4ccc-a14b-ce5e8b2be69e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_Levy_generator_nonlinear_large_negative2_mark_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = Measure.dirac (-2 : ℝ))
    (y : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5) :
    (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand
        (fun z : ℝ => if z < 0 then 0 else 1 + z + z ^ 2)
        y z ∂X.ν) = -(1 + y + y ^ 2) := by
  have hAt :
      SpectrallyNegativeLevy.generatorIntegrand
        (fun z : ℝ => if z < 0 then 0 else 1 + z + z ^ 2)
        y (-2 : ℝ) = -(1 + y + y ^ 2) :=
    avram_jump6_A_original_Levy_generator_nonlinear_large_negative2_mark_exact
      y hy hcap
  simp [hν, setIntegral_dirac, hAt]
