-- Prove2me | solution 1 for AvramDividend.Classical.avram_a28_sigma_zero_gaussian_source_laplace_exact_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:03:13.182611+00:00
-- url     : https://prove2.me/submissions/8c99b286-6851-4f5d-8f96-224e10f62ce2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
import Theorems.Thm_AvramDividend_Classical_laplaceExponent_zero_jump_measure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original intrinsic Gaussian residual has the exact trivial Gaussian Laplace law at zero sigma. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (hSigma : X.σ = 0)
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ (t : ℝ≥0) (θ : ℝ), 0 ≤ θ →
      Integrable (fun ω => Real.exp (θ * G t ω)) P ∧
      (∫ ω, Real.exp (θ * G t ω) ∂P) =
        Real.exp ((t : ℝ) *
          laplaceExponent 0 X.σ (0 : Measure ℝ) θ) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hRzero :=
    avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
      X hX hFinite R hR hSigma
  intro t θ _
  have hGzero : ∀ᵐ ω ∂P, G t ω = 0 := by
    filter_upwards [hEq, hRzero] with ω hGω hRω
    rw [hGω t, hRω t]
  have hExp : (fun ω => Real.exp (θ * G t ω)) =ᵐ[P]
      (fun _ : Ω => (1 : ℝ)) := by
    filter_upwards [hGzero] with ω hω
    simp [hω]
  have hInt : Integrable (fun _ : Ω => (1 : ℝ)) P :=
    integrable_const 1
  refine ⟨hInt.congr hExp.symm, ?_⟩
  calc
    (∫ ω, Real.exp (θ * G t ω) ∂P) =
      (∫ _ : Ω, (1 : ℝ) ∂P) := integral_congr_ae hExp
    _ = 1 := by simp
    _ = Real.exp ((t : ℝ) *
          laplaceExponent 0 X.σ (0 : Measure ℝ) θ) := by
      rw [hSigma, laplaceExponent_zero_jump_measure]
      norm_num
