-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_finite_horizon_expected_budget_from_ito
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:33:40.997808+00:00
-- url     : https://prove2.me/submissions/bf37d868-99dc-4333-bfb7-0de8690f7cca

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_cash_integrability_and_budget_from_ito
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The genuine bounded original stopping clock and nonnegative boundary
reward discharge all non-stochastic side conditions of the expected budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (W Cash Term M G H : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_pos : ∀ y : ℝ, 0 < y → 0 ≤ w y)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermI : Integrable Term P)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hGnonpos : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hHnonpos : ∀ᵐ ω ∂P, H ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      Term ω + Cash ω = w x + M ω + G ω + H ω) :
    Integrable Cash P ∧
      ((∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
        (∫ ω, Cash ω ∂P) ≤ w x) := by
  have hwNonneg : ∀ y : ℝ, 0 ≤ w y := by
    intro y
    rcases lt_trichotomy y 0 with hy | hy | hy
    · simp [hw_neg y hy]
    · simpa [hy] using hw0
    · exact hw_pos y hy
  have hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω := by
    filter_upwards [] with ω
    rw [hTerm ω]
    exact mul_nonneg (Real.exp_pos _).le (hwNonneg (W ω))
  have hCashFinite :=
    avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
      X x C D hD q τ T hτBound
  exact avram_wave6_06_original_cash_integrability_and_budget_from_ito
    X x C D hD q hq τ T hτBound hτ hτruin
    W Cash Term M G H hW hCash hCashFinite
    w hTerm hTermI hMI hGI hHI
    hTermNonneg hMzero hGnonpos hHnonpos hIto
