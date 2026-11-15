-- Prove2me | solution 1 for AvramDividend.Classical.avram_a29_sigma_zero_gaussian_intrinsic_raw_allpath_regularity_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:06:13.364511+00:00
-- url     : https://prove2.me/submissions/d3359d64-098d-4970-b191-f5d4878feeae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a22_zero_noise_original_filtered_levy_witness
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At zero Gaussian volatility the constant-zero original raw-adapted Levy witness regularises the intrinsic residual on all paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSigma : X.σ = 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ ω t, ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ ω t, 0 < t →
        ∃ l, Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l)) ∧
      (∀ ω t l, 0 < t →
        Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l) →
        G t ω ≤ l) := by
  obtain ⟨Y, _, _, hYZero⟩ :=
    avram_a22_zero_noise_original_filtered_levy_witness X
  have hRZero :=
    avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
      X hX hFinite R hR hSigma
  refine ⟨Y.X, Y.adapted, Y.X_zero, ?_, Y.rightCont, Y.leftLim,
    Y.noPosJumps⟩
  filter_upwards [hRZero] with ω hω
  intro t
  rw [hYZero t ω, hω t]
