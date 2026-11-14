-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_residual_retained_zero_time_quadratic_package_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:41:14.061326+00:00
-- url     : https://prove2.me/submissions/595e83af-42ed-40c1-aaf9-eccb300ed84e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every physical Gaussian residual and retained-band quadratic cross term vanishes at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n 0 ω)^2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n 0 ω)^2 ∂P) = 0 ∧
      Integrable (fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n 0 ω *
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n 0 ω) P ∧
      (∫ ω,
        avram_p4_h_gaussian_intrinsic_truncated_residual X n 0 ω *
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n 0 ω ∂P) = 0 := by
  simp [avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin,
    avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_time]
