-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja21_original_gaussian_core_and_jump_cutoff_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:45:31.888358+00:00
-- url     : https://prove2.me/submissions/7efe713c-17ae-4aad-9207-da5117f6ff65

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_anoise33_original_smallband_compensator_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (t : ℝ≥0) :
    Measurable[𝓕 t]
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
        avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) ∧
    Measurable[𝓕 t]
      (fun ω => -avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) := by
  constructor
  · exact (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X 0 t).add
      (avram_anoise33_original_smallband_compensator_adapted X 0 t)
  · exact (avram_anoise33_original_smallband_compensator_adapted
      X n t).neg
