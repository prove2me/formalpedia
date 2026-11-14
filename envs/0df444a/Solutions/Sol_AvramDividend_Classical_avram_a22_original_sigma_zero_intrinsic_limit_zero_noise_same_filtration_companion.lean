-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_sigma_zero_intrinsic_limit_zero_noise_same_filtration_companion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:43:13.359958+00:00
-- url     : https://prove2.me/submissions/0e44df75-f5a2-46f3-bdbb-f1e9a06322cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a22_zero_noise_original_filtered_levy_witness
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_zero_path_zero_nu_zero_sigma_forces_zero_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- In the zero-Gaussian case the actual original residual is zero, realised by a zero-source Levy companion. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hSigma : X.σ = 0) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        R t ω = Y.X t ω - (t : ℝ) * Y.c) := by
  obtain ⟨Y, hNu, hSig, hPath⟩ :=
    avram_a22_zero_noise_original_filtered_levy_witness X
  have hC :=
    avram_a22_original_zero_path_zero_nu_zero_sigma_forces_zero_drift
      Y hNu hSig hPath
  have hRZero :=
    avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
      X hX hFinite R hR hSigma
  refine ⟨Y, hNu, ?_, ?_⟩
  · rw [hSig, hSigma]
  · filter_upwards [hRZero] with ω hω
    intro t
    rw [hω t, hPath t ω, hC]
    ring
