-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_finite_band_drift_renormalization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:29:12.644967+00:00
-- url     : https://prove2.me/submissions/301049a5-0e48-4f53-8b34-d0442198483b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_band_raw_increment_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hgen : X.GeneratorIntegrable w y) :
    X.c * deriv w y +
      (∫ z in Ioo (-1 : ℝ) (-ε),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) =
      (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w y +
      (∫ z in Ioo (-1 : ℝ) (-ε), w (y + z) - w y ∂X.ν) := by
  rw [avram_p4_c_generator_finite_band_raw_increment_identity X w y ε hε hgen]
  ring
