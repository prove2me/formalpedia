-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_infiniteactivity_full_negative_generator_lower_from_smallcomp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:31:09.616619+00:00
-- url     : https://prove2.me/submissions/29db8021-fe81-4383-be51-a6e546f9a14c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_generator_true_negative_integral_exact_large_small_unit_split
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_large_negative_jump_generator_integral_lower_floor
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (y : ℝ)
    (hwpos : ∀ u : ℝ, 0 ≤ w u)
    (hderiv : 0 ≤ deriv w y)
    (hGen : X.GeneratorIntegrable w y) :
    (∫ z in Ioo (-1 : ℝ) 0,
      SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) -
      (X.ν (Iic (-1 : ℝ))).toReal * w y ≤
    (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by
  have hSplit :=
    avram_f6_original_generator_true_negative_integral_exact_large_small_unit_split
      X w y hGen
  have hLarge :=
    avram_f6_original_large_negative_jump_generator_integral_lower_floor
      X w y hwpos hderiv hGen
  linarith
