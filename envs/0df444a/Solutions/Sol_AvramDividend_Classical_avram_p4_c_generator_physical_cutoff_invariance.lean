-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_physical_cutoff_invariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:04:18.206311+00:00
-- url     : https://prove2.me/submissions/9950495c-7098-4599-bfca-aaa4cf1aedd1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_original_epsilon_drift_identification

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hgen : X.GeneratorIntegrable w y) :
    let F : ℝ → ℝ := fun η =>
      X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-η), z ∂X.ν)) * deriv w y +
        (∫ z in Iic (-1 : ℝ), w (y + z) - w y ∂X.ν) +
        (∫ z in Ioo (-1 : ℝ) (-η), w (y + z) - w y ∂X.ν) +
        (∫ z in Ico (-η) 0,
          SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν)
    F ε = F δ := by
  dsimp only
  have hεid :=
    avram_p4_c_generator_original_epsilon_drift_identification
      X w y ε hε hε1 hgen
  have hδid :=
    avram_p4_c_generator_original_epsilon_drift_identification
      X w y δ hδ hδ1 hgen
  exact hεid.symm.trans hδid
