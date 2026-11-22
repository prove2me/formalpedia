-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_original_finiteactivity_intrinsic_continuous_gaussian_centered_martingale_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T22:45:13.801072+00:00
-- url     : https://prove2.me/submissions/56e73dee-4619-4976-ba44-582aa8494b3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The intrinsic finite-activity Gaussian component has a canonical
original-space continuous centred martingale version with independent
stationary increments, without an assumed limit-process witness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ (R G : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (R t ω))) ∧
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) ∧
      (∀ s T : ℝ≥0,
        Indep (MeasurableSpace.comap
          (fun ω => G (s + T) ω - G s ω) inferInstance)
          (𝓕 s) P) ∧
      (∀ T, ∃ Z : Ω → ℝ, Measurable Z ∧
        ∀ s : ℝ≥0,
          Measure.map (fun ω => G (s + T) ω - G s ω) P =
            Measure.map Z P) ∧
      (∀ t : ℝ≥0, Integrable (G t) P ∧
        (∫ ω, G t ω ∂P) = 0) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (G t) ω = G s ω) := by
  obtain ⟨R, hR⟩ :=
    avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
      X hFinite
  have hSource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)) :=
    hR.mono (fun ω hω => hω.1)
  obtain ⟨G, hAdapt, hZero, hEqual, hContinuous, hIndependent,
      hStationary, hCentred, hMartingale⟩ :=
    avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
      X hX hFinite R hSource
  exact ⟨R, G, hSource, hAdapt, hZero, hEqual,
    hContinuous, hIndependent, hStationary, hCentred, hMartingale⟩

