-- Prove2me | solution 1 for AvramDividend.Classical.avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:16:15.682207+00:00
-- url     : https://prove2.me/submissions/681b48bb-361e-4fa9-8d3f-7ca59208e41d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_finite_range_mixed_stopped_noise_pair
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Both original physical finite-range stopped Gaussian and compensated jump noises exist and are initially centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S) :
    ∃ (R Jsmall : ℝ≥0 → Ω → ℝ) (MG MJ : Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto
          (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (R t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto
          (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (Jsmall t ω))) ∧
      (∀ t : ℝ≥0, Integrable (R t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (R t) ω = R s ω) ∧
      (∀ t : ℝ≥0, Integrable (Jsmall t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (Jsmall t) ω = Jsmall s ω) ∧
      Integrable MG P ∧ Integrable MJ P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P MG ω = 0) ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P MJ ω = 0) ∧
      (∀ ω, MG ω = R (τ ω) ω) ∧
      (∀ ω, MJ ω = Jsmall (τ ω) ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, hRlim, hRadapt, hRint, hRmart⟩ :=
    avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
      X hX hFinite
  have hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)) := by
    filter_upwards [hRlim] with ω hω
    exact hω.1
  obtain ⟨MG, MJ, hMGint, hMJint, hMGzero, hMJzero,
      hMGsource, Jsmall, hJsource, hJint, hJmart, hMJsource⟩ :=
    avram_jb20_original_finite_range_mixed_stopped_noise_pair
      X hX hFinite n hn τ hτstop hτbound S hτrange
      R hRsource hRint hRmart
  exact ⟨R, Jsmall, MG, MJ, hRsource, hJsource,
    hRint, hRmart, hJint, hJmart,
    hMGint, hMJint, hMGzero, hMJzero, hMGsource, hMJsource⟩
