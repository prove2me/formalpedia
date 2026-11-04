-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_original_epsilon_drift_identification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:52:31.618951+00:00
-- url     : https://prove2.me/submissions/7c8cb3c7-fef4-4fda-a67d-a4aafb681a88

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_negative_mark_integral_cutoff_split
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_large_cutoff_unit_partition
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_band_drift_renormalization
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative_integral_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hgen : X.GeneratorIntegrable w y) :
    X.generator w y =
      X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
      (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w y +
      (∫ z in Iic (-1 : ℝ), w (y + z) - w y ∂X.ν) +
      (∫ z in Ioo (-1 : ℝ) (-ε), w (y + z) - w y ∂X.ν) +
      (∫ z in Ico (-ε) 0,
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by
  have hsplit :=
    avram_p4_c_generator_negative_mark_integral_cutoff_split X w y ε hε hgen
  have hbig :=
    avram_p4_c_generator_large_cutoff_unit_partition X w y ε hε hε1 hgen
  have hlarge := generatorIntegrand_large_negative_integral_identity w y X.ν
  have hdrift :=
    avram_p4_c_generator_finite_band_drift_renormalization X w y ε hε hgen
  change (X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
    X.c * deriv w y +
    (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν)) = _
  rw [hsplit, hbig, hlarge]
  linear_combination hdrift
