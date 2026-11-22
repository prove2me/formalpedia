-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_original_bounded_clock_continuous_gaussian_smallmark_both_eventwise_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T23:09:01.483857+00:00
-- url     : https://prove2.me/submissions/22ef6237-4fc1-4d30-8d6c-3c95a56dc00f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
import Theorems.Thm_AvramDividend_Classical_avram_ja18_intrinsic_gaussian_bounded_true_stop_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin17_original_bounded_band_compensated_stopped_martingale_public
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the original true physical stopped clock, both the continuous Gaussian
and compensated negative smallmark channels have zero expectation on every
initial-filtration event; neither process is assumed as an input. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    ∃ (G Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (G t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (Jsmall t ω))) ∧
      Integrable (fun ω => G (τ ω) ω) P ∧
      Integrable (fun ω => Jsmall (τ ω) ω) P ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A, G (τ ω) ω ∂P) = 0 ∧
        (∫ ω in A, Jsmall (τ ω) ω ∂P) = 0) := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, hR⟩ :=
    avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
      X hFinite
  have hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)) :=
    hR.mono (fun ω hω => hω.1)
  obtain ⟨G, _hAdapt, _hZero, hSame, hCont, _hIndep,
      _hStationary, hCenter, hMart⟩ :=
    avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
      X hX hFinite R hRsource
  have hGsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (G t ω)) := by
    filter_upwards [hRsource, hSame] with ω hlim hEq
    intro t
    simpa only [hEq t] using hlim t
  obtain ⟨hGI, hGzero⟩ :=
    avram_ja18_intrinsic_gaussian_bounded_true_stop_condexp_zero
      X hX hFinite G hGsource (fun t => (hCenter t).1)
      hMart n hn τ hτstop hτbound
  obtain ⟨Jsmall, hJsource, _hJint, _hJmart, hJI, hJzero⟩ :=
    avram_mix_fin17_original_bounded_band_compensated_stopped_martingale_public
      X hX hFinite n hn τ hτstop hτbound
  have hEvent : ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, G (τ ω) ω ∂P) = 0 ∧
      (∫ ω in A, Jsmall (τ ω) ω ∂P) = 0 := by
    intro A hA
    constructor
    · exact avram_ubv_jump11_past_event_integral_of_condexp_zero
        (𝓕.rightCont 0) (𝓕.rightCont.le 0)
        (fun ω => G (τ ω) ω) hGI hGzero A hA
    · exact avram_ubv_jump11_past_event_integral_of_condexp_zero
        (𝓕.rightCont 0) (𝓕.rightCont.le 0)
        (fun ω => Jsmall (τ ω) ω) hJI hJzero A hA
  exact ⟨G, Jsmall, hCont, hGsource, hJsource, hGI, hJI, hEvent⟩

