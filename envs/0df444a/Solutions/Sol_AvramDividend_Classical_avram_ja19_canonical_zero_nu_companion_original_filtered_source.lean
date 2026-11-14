-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_canonical_zero_nu_companion_original_filtered_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:41:44.304004+00:00
-- url     : https://prove2.me/submissions/a750f7b8-955e-4566-ab77-8fca91529609
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_sigma_zero_intrinsic_limit_zero_noise_same_filtration_companion
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_positive_sigma_intrinsic_limit_true_same_filtration_gaussian_companion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Construct the canonical same-filtered Gaussian witness from its true sigma branches. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto
          (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (Y.X t ω - (t : ℝ) * Y.c))) := by
  obtain ⟨R, hLimit, _hAdapt⟩ :=
    avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted X hFinite
  have hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)) := by
    filter_upwards [hLimit] with ω hω
    exact hω.1
  obtain ⟨Y, hNu, hSigma, hYR⟩ :
      ∃ Y : SpectrallyNegativeLevy P 𝓕,
        Y.ν = 0 ∧ Y.σ = X.σ ∧
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
          R t ω = Y.X t ω - (t : ℝ) * Y.c) := by
    rcases lt_or_eq_of_le X.σ_nonneg with hPos | hZero
    · exact
        avram_a22_original_positive_sigma_intrinsic_limit_true_same_filtration_gaussian_companion
          X hX hFinite R hR hPos
    · exact
        avram_a22_original_sigma_zero_intrinsic_limit_zero_noise_same_filtration_companion
          X hX hFinite R hR hZero.symm
  refine ⟨Y, hNu, hSigma, ?_⟩
  filter_upwards [hR, hYR] with ω hRω hYRω
  intro t
  simpa only [hYRω t] using (hRω t)
