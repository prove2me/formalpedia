-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_actual_positive_clock_finitecap_full_reward_with_same_initially_centered_G_J
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T23:15:09.755+00:00
-- url     : https://prove2.me/submissions/d63d6185-fb0e-4078-9494-2554bc2269ee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_bounded_clock_continuous_gaussian_smallmark_both_eventwise_centered
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_allnu_finitecap_canonical_stopped_full_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_all_stopped_clocks_le_integer_horizon
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_ruinclipped_stopped_reserve_full_threechannel_source
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original finite-cap positive-clock stopped reward, expressed
through the SAME constructed physical Gaussian and compensated small jumps
whose stopped integrals are initially centred on the positive-clock event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    let A : Set Ω := {ω | τ ω ≠ 0}
    ∃ (G Jsmall : ℝ≥0 → Ω → ℝ),
      MeasurableSet[𝓕.rightCont 0] A ∧
      Integrable (fun ω => Term ω + Cash ω) P ∧
      Integrable (fun ω => G (τ ω) ω) P ∧
      Integrable (fun ω => Jsmall (τ ω) ω) P ∧
      (∫ ω in A, G (τ ω) ω ∂P) = 0 ∧
      (∫ ω in A, Jsmall (τ ω) ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω =
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + (τ ω : ℝ) * X.c +
            G (τ ω) ω + Jsmall (τ ω) ω +
            avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω -
            (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
             then rightLimit D (τ ω) ω else D (τ ω) ω)) + Cash ω) := by
  intro A
  have hBound : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
    have h := avram_jump6_B_original_all_stopped_clocks_le_integer_horizon
      X x D n τ hτeq (fun _ : ℕ => τ) (by intro k ω; exact le_refl _)
    exact fun ω => h 0 ω
  obtain ⟨hTermM, _hCashI, _hTermI, hFullI, hEvent⟩ :=
    avram_jump6_original_allnu_finitecap_canonical_stopped_full_reward_L1
      X x C hCfinite hxc w hw_cont hw_neg D hD
      q (le_of_lt hq) n τ hτeq hτmeas hτstop
      W Cash Term hW hCash hTerm
  obtain ⟨G, Jsmall, _hGcont, hGsource, hJsource,
      hGI, hJI, hEventBoth⟩ :=
    avram_jump6_original_bounded_clock_continuous_gaussian_smallmark_both_eventwise_centered
      X hX hFinite n hn τ hτstop hBound
  obtain ⟨hGzero, hJzero⟩ := hEventBoth A hEvent
  have hWsource :=
    avram_ja18_original_ruinclipped_stopped_reserve_full_threechannel_source
      X x D τ W hW G Jsmall hGsource hJsource
  have hExact : ∀ᵐ ω ∂P, Term ω + Cash ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (x + (τ ω : ℝ) * X.c +
          G (τ ω) ω + Jsmall (τ ω) ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω -
          (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
           then rightLimit D (τ ω) ω else D (τ ω) ω)) + Cash ω := by
    filter_upwards [hWsource] with ω hw
    calc
      Term ω + Cash ω =
          Real.exp (-(q * (τ ω : ℝ))) * w (W ω) + Cash ω := by
        rw [hTerm ω]
      _ = _ := by rw [hw]
  exact ⟨G, Jsmall, hEvent, hFullI, hGI, hJI,
    hGzero, hJzero, hExact⟩

