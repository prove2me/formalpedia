-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_finiteactivity_true_ruinclipped_terminal_original_continuous_G_and_centered_Jsmall
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T22:48:18.112072+00:00
-- url     : https://prove2.me/submissions/2f04719e-807b-48e5-af30-bd8e8d81051b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_all_stopped_clocks_le_integer_horizon
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin17_original_bounded_band_compensated_stopped_martingale_public
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_ruinclipped_stopped_reserve_full_threechannel_source
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original ruin-clipped postpayment terminal using a continuous Gaussian
martingale and initially centred small-jump source on the same Ω and clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∃ (G Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) ∧
      (∀ t : ℝ≥0, Integrable (G t) P ∧
        (∫ ω, G t ω ∂P) = 0) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (G t) ω = G s ω) ∧
      (∀ t : ℝ≥0, Integrable (Jsmall t) P) ∧
      Integrable (fun ω => Jsmall (τ ω) ω) P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P
          (fun η => Jsmall (τ η) η) ω = 0) ∧
      (∀ᵐ ω ∂P, W ω =
        x + (τ ω : ℝ) * X.c + G (τ ω) ω + Jsmall (τ ω) ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω -
        (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
         then rightLimit D (τ ω) ω else D (τ ω) ω)) := by
  obtain ⟨R, hR⟩ :=
    avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
      X hFinite
  have hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)) :=
    hR.mono (fun ω hω => hω.1)
  obtain ⟨G, hAdapt, hZero, hGsame, hCont, _hIndep, _hStat,
      hCentred, hMart⟩ :=
    avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
      X hX hFinite R hRsource
  have hBound : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
    have h := avram_jump6_B_original_all_stopped_clocks_le_integer_horizon
      X x D n τ hτeq (fun _ : ℕ => τ) (by intro k ω; exact le_refl _)
    exact fun ω => h 0 ω
  obtain ⟨Jsmall, hJsource, hJintegrable, _hJmart, hJstopI, hJstop0⟩ :=
    avram_mix_fin17_original_bounded_band_compensated_stopped_martingale_public
      X hX hFinite n hn τ hτstop hBound
  have hWpath :=
    avram_ja18_original_ruinclipped_stopped_reserve_full_threechannel_source
      X x D τ W hW R Jsmall hRsource hJsource
  have hWwithG : ∀ᵐ ω ∂P, W ω =
      x + (τ ω : ℝ) * X.c + G (τ ω) ω + Jsmall (τ ω) ω +
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω -
      (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
       then rightLimit D (τ ω) ω else D (τ ω) ω) := by
    filter_upwards [hWpath, hGsame] with ω hw hsame
    simpa only [hsame (τ ω)] using hw
  exact ⟨G, Jsmall, hAdapt, hZero, hCont, hCentred, hMart,
    hJintegrable, hJstopI, hJstop0, hWwithG⟩

