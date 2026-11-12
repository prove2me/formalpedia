-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja21_original_cutoff_residual_gaussian_core_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:45:34.720745+00:00
-- url     : https://prove2.me/submissions/0079e65e-53d8-4741-ba58-6904dd6e334f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
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
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω =
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
       avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω := by
  have h :=
    avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
      X n 0 t ω
  linarith
