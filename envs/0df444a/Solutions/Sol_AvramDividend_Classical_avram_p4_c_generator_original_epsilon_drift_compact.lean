-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_original_epsilon_drift_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:01:28.112736+00:00
-- url     : https://prove2.me/submissions/303f3953-1ce7-4f34-b24f-ef10c97bf9c2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_original_epsilon_drift_identification
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_raw_large_cutoff_unit_partition

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
      (∫ z in Iio (-ε), w (y + z) - w y ∂X.ν) +
      (∫ z in Ico (-ε) 0,
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by
  have hFormula :=
    avram_p4_c_generator_original_epsilon_drift_identification
      X w y ε hε hε1 hgen
  have hRaw :=
    avram_p4_c_generator_raw_large_cutoff_unit_partition
      X w y ε hε hε1 hgen
  rw [hFormula, hRaw]
  ring
