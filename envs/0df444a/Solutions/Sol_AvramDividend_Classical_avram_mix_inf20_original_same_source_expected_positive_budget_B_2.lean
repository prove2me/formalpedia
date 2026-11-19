-- Prove2me | solution 2 for AvramDividend.Classical.avram_mix_inf20_original_same_source_expected_positive_budget_B
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:53:53.331857+00:00
-- url     : https://prove2.me/submissions/cee8ceb1-36f4-4e3f-a0a6-27ac86acdee2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_grid_compensated_hjb_certificate_mission_public
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_ruin_source_grid_asymptotic_dividend_upper
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_supported_mean_zero_event_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ k, (∫ ω in {ω : Ω | σ k ω ≠ 0}, F k ω ∂P) ≤
      w x * (P {ω : Ω | σ k ω ≠ 0}).toReal := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  let Cash : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let Term : Ω → ℝ := fun ω =>
    Real.exp (-(q * (σ k ω : ℝ))) *
      w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
        else riskProcess X x D (σ k ω) ω)
  obtain ⟨u, meshCount, Source, Dividend, Mc, G, R,
      hmono, hzero, hcover, hruin, hSource, hDividend,
      hMcI, hGI, hRI, hMcMean, hMcZero, hGsign, hRsign,
      hSourceLim, hDivLim⟩ :=
    avram_jump6_B_original_physical_grid_compensated_hjb_certificate_mission_public
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτstop σ F hσstop hσle hFsource hFI
      hInfiniteActivity k
  have hDstrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) := by
    intro ω
    rfl
  have hupper : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ w x + Mc ω + G ω + R ω :=
    avram_wave6_06_original_ruin_source_grid_asymptotic_dividend_upper
      X x q D hDstrategy w (σ k) hruin u meshCount
      hmono hzero hcover Term Cash Mc G R Source Dividend
      hTerm hSource hDividend hSourceLim hDivLim
  have hReward : ∀ ω, F k ω = Term ω + Cash ω := by
    intro ω
    simpa only [Term, Cash] using hFsource k ω
  let A : Set Ω := {ω | σ k ω ≠ 0}
  have hA : MeasurableSet A :=
    (avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
      𝓕 (σ k) (hσstop k)).compl
  have hMoff : ∀ᵐ ω ∂P, ω ∉ A → Mc ω = 0 := by
    filter_upwards [hMcZero] with ω hω hn
    exact hω (by simpa [A] using hn)
  have hSimpleUpper : ∀ᵐ ω ∂P, F k ω ≤ w x + Mc ω := by
    filter_upwards [hupper, hGsign, hRsign] with ω hu hg hr
    rw [hReward ω]
    linarith only [hu, hg, hr]
  have hBound :=
    avram_mix_inf15_supported_mean_zero_event_budget
      A hA (w x) (F k) Mc (hFI k) hMcI
      hMcMean hMoff hSimpleUpper
  simpa only [A] using hBound
