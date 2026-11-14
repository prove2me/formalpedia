-- Prove2me | solution 3 for AvramDividend.Classical.avram_anoise22_original_gaussian_cutoff_exact_second_moment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:22:04.051724+00:00
-- url     : https://prove2.me/submissions/106312fb-1506-4af0-8505-825a487cec31
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_cutoff_gaussian_plus_all_smallmarks_second_moment_20261113_v2
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_residual_retained_smallmark_self_covariance_20261113_v2
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_difference_variance_of_self_covariance_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_negative_quadratic_cutoff_integral_partition_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_retained_smallband_exact_variance_20261112
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Correct original Gaussian finite-cutoff second moment from the original
zero-cutoff moment and physical retained-jump self covariance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2 ∂P) =
        (t : ℝ) * X.σ ^ 2 +
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by
  intro n t
  let R0 : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω
  let J : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω
  let Rn : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω
  have hZero := avram_a21_original_zero_cutoff_gaussian_plus_all_smallmarks_second_moment_20261113_v2
    X hX hFinite t
  change Integrable (fun ω => (R0 ω)^2) P ∧
    (∫ ω, (R0 ω)^2 ∂P) =
      (t : ℝ) * X.σ ^ 2 + (t : ℝ) *
        (∫ z in Ioo (-1 : ℝ) 0, z ^ 2 ∂X.ν) at hZero
  have hCross := avram_a21_original_zero_residual_retained_smallmark_self_covariance_20261113_v2
    X hX hFinite n t
  change Integrable (fun ω => (J ω)^2) P ∧
    Integrable (fun ω => R0 ω * J ω) P ∧
      (∫ ω, R0 ω * J ω ∂P) = (∫ ω, (J ω)^2 ∂P) at hCross
  have hDiff := avram_a21_original_difference_variance_of_self_covariance_20261113
    P R0 J hZero.1 hCross.1 hCross.2.1 hCross.2.2
  have hVar := avram_a21_original_retained_smallband_exact_variance_20261112
    X hX hFinite n t
  have hPart := avram_a21_original_negative_quadratic_cutoff_integral_partition_20261113
    X.ν hFinite n
  have hPath : ∀ ω, Rn ω = R0 ω - J ω := by
    intro ω
    calc
      Rn ω = (R0 ω +
        avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) - J ω :=
          avram_ja21_original_cutoff_residual_gaussian_core_split X n t ω
      _ = R0 ω - J ω := by
        rw [avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff]
        ring
  have hEq : (fun ω => (Rn ω)^2) = (fun ω => (R0 ω - J ω)^2) := by
    funext ω
    rw [hPath ω]
  change Integrable (fun ω => (Rn ω)^2) P ∧
    (∫ ω, (Rn ω)^2 ∂P) = (t : ℝ) * X.σ ^ 2 +
      (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0,
        z ^ 2 ∂X.ν)
  rw [hEq]
  refine ⟨hDiff.1, ?_⟩
  calc
    (∫ ω, (R0 ω - J ω)^2 ∂P) =
      (∫ ω, (R0 ω)^2 ∂P) - (∫ ω, (J ω)^2 ∂P) := hDiff.2
    _ = (t : ℝ) * X.σ ^ 2 +
        (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0,
          z ^ 2 ∂X.ν) := by
      rw [hZero.2, hVar, hPart]
      ring
