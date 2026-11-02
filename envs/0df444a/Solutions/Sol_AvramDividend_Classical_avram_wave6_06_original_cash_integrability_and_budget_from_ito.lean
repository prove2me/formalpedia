-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_cash_integrability_and_budget_from_ito
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:13:52.041418+00:00
-- url     : https://prove2.me/submissions/587e4bd6-76c5-4cf7-8c12-e0b21f6de1a2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_actual_stopped_expected_budget_from_ito_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Cash integrability follows from an integrable stopped Ito-Meyer decomposition;
the existing original-source expectation theorem then gives both bounds. -/
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
    (hTermI : Integrable Term P)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hGnonpos : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hHnonpos : ∀ᵐ ω ∂P, H ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      Term ω + Cash ω = w x + M ω + G ω + H ω) :
    Integrable Cash P ∧
      ((∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
        (∫ ω, Cash ω ∂P) ≤ w x) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hConst : Integrable (fun _ : Ω => w x) P := integrable_const _
  have hRight : Integrable (fun ω => w x + M ω + G ω + H ω) P :=
    ((hConst.add hMI).add hGI).add hHI
  have hCashEq :
      (fun ω => w x + M ω + G ω + H ω - Term ω) =ᵐ[P] Cash := by
    filter_upwards [hIto] with ω heq
    linarith only [heq]
  have hCashI : Integrable Cash P := (hRight.sub hTermI).congr hCashEq
  refine ⟨hCashI, ?_⟩
  exact avram_wave6_06_actual_stopped_expected_budget_from_ito_decomposition
    X x C D hD q hq τ T hτBound hτ hτruin
    W Cash Term M G H hW hCash hCashFinite
    w hTerm hTermI hCashI hMI hGI hHI
    hTermNonneg hMzero hGnonpos hHnonpos hIto
