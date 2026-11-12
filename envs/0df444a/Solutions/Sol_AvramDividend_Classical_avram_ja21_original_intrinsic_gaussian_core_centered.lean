-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja21_original_intrinsic_gaussian_core_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:57:46.957592+00:00
-- url     : https://prove2.me/submissions/7f1478e8-bfec-412f-b3be-2cd8e577cbb1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_zero_cutoff_increment_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_time
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum_zero_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0, (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
        avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) ∂P) = 0 := by
  intro t
  have hRzero : ∀ ω, avram_p4_h_gaussian_intrinsic_truncated_residual X 0 0 ω = 0 := by
    intro ω
    simp [avram_p4_h_gaussian_intrinsic_truncated_residual,
      X.X_zero, avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_time,
      avram_p4_h_gaussian_intrinsic_large_jump_sum_zero_time]
  have hRmean : (∫ ω, avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω ∂P) = 0 := by
    have h := (avram_ja18g_original_zero_cutoff_increment_mean_zero X hX hFinite)
      0 t (zero_le : (0 : ℝ≥0) ≤ t)
    simpa only [hRzero, sub_zero] using h
  have hBandZero : ∀ ω, avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω = 0 := by
    intro ω
    exact avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff X t ω
  simpa only [hBandZero, add_zero] using hRmean
