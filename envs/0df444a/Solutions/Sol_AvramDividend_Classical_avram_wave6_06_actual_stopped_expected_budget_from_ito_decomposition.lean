-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_actual_stopped_expected_budget_from_ito_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:38:31.554279+00:00
-- url     : https://prove2.me/submissions/8da531d9-698e-4410-90a7-f74e52b1106e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Expected terminal-plus-dividend and cash-only bounds from a separately
verified same-source stopped Ito-Meyer identity and its signed remainders. -/
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
    (hCashFinite : ∀ᵐ ω ∂P,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤)
    (w : ℝ → ℝ)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermI : Integrable Term P) (hCashI : Integrable Cash P)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hGnonpos : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hHnonpos : ∀ᵐ ω ∂P, H ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      Term ω + Cash ω = w x + M ω + G ω + H ω) :
    (∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
      (∫ ω, Cash ω ∂P) ≤ w x := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hGmean : (∫ ω, G ω ∂P) ≤ 0 :=
    integral_nonpos_of_ae hGnonpos
  have hHmean : (∫ ω, H ω ∂P) ≤ 0 :=
    integral_nonpos_of_ae hHnonpos
  have hTermMean : 0 ≤ (∫ ω, Term ω ∂P) :=
    integral_nonneg_of_ae hTermNonneg
  have hBalance :
      (∫ ω, Term ω + Cash ω ∂P) =
        w x + (∫ ω, M ω ∂P) +
          (∫ ω, G ω ∂P) + (∫ ω, H ω ∂P) := by
    calc
      _ = ∫ ω, w x + M ω + G ω + H ω ∂P :=
        integral_congr_ae hIto
      _ = _ := by
        simp [integral_add, hMI, hGI, hHI, add_assoc]
  have hBudget : (∫ ω, Term ω + Cash ω ∂P) ≤ w x := by
    rw [hBalance, hMzero]
    linarith only [hGmean, hHmean]
  constructor
  · exact hBudget
  · rw [integral_add hTermI hCashI] at hBudget
    linarith only [hBudget, hTermMean]
