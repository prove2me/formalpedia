-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_finiteactivity_zero_sigma_cutoff_physical_square_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:32:07.809624+00:00
-- url     : https://prove2.me/submissions/90b3c4c7-01b2-40f2-9e1a-3b2521137d62

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_anoise21_original_gaussian_residual_L2_cutoff_error
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original finite-activity zero-Gaussian residual square integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSigma : X.σ = 0) (T : ℝ≥0) :
    Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 T ω) ^ 2) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, hR⟩ :=
    avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
      X hFinite
  have hSource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j u ω)
        atTop (nhds (R u ω)) := by
    filter_upwards [hR] with ω hω
    exact hω.1
  have hRzero : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, R u ω = 0 :=
    avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
      X hX hFinite R hSource hSigma
  have hCutMeas (j : ℕ) : AEStronglyMeasurable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X j T ω)
      P := by
    exact ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X j T).mono (𝓕.le T) le_rfl).aestronglyMeasurable
  have hSourceT : ∀ᵐ ω ∂P,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j T ω)
        atTop (nhds (R T ω)) := by
    filter_upwards [hSource] with ω hω
    exact hω T
  have hRmeas : AEStronglyMeasurable (R T) P :=
    aestronglyMeasurable_of_tendsto_ae atTop hCutMeas hSourceT
  have hErr := (avram_anoise21_original_gaussian_residual_L2_cutoff_error
    X hFinite R T hSourceT hRmeas hCutMeas 0).1
  have hEq : (fun ω =>
      (R T ω - avram_p4_h_gaussian_intrinsic_truncated_residual
        X 0 T ω) ^ 2) =ᵐ[P]
      (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual
        X 0 T ω) ^ 2) := by
    filter_upwards [hRzero] with ω hω
    simp [hω T]
  exact hErr.congr hEq
