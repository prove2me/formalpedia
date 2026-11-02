-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_closed_clock_budget_from_joint_hjb_ito
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:37:57.992663+00:00
-- url     : https://prove2.me/submissions/97c098e1-daad-4138-94a2-9c6a0005336b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_cash_integrability_and_budget_from_ito
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_inclusive_random_clock_real_cash_budget_to_ennreal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original inclusive-clock expected payout bound conditional on the genuine
same-path stopped Itô–Meyer identity. -/
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
    (hGHnonpos : ∀ᵐ ω ∂P, G ω + H ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      Term ω + Cash ω = w x + M ω + G ω + H ω) :
    Integrable Cash P ∧
      (∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
      (∫ ω, Cash ω ∂P) ≤ w x ∧
      (∫⁻ ω, ∫⁻ s in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by
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
  letI : IsProbabilityMeasure P := X.isProbability
  have hGsumI : Integrable (fun ω => G ω + H ω) P := hGI.add hHI
  have hZeroI : Integrable (fun _ : Ω => (0 : ℝ)) P := integrable_const _
  have hZeroNonpos : ∀ᵐ ω ∂P, (0 : ℝ) ≤ 0 := by
    filter_upwards [] with ω
    exact le_rfl
  have hItoJoint : ∀ᵐ ω ∂P,
      Term ω + Cash ω = w x + M ω + (G ω + H ω) + 0 := by
    filter_upwards [hIto] with ω heq
    linarith only [heq]
  have hBudget :=
    avram_wave6_06_original_cash_integrability_and_budget_from_ito
      X x C D hD q hq τ T hτBound hτ hτruin
      W Cash Term M (fun ω => G ω + H ω) (fun _ => 0)
      hW hCash hCashFinite w hTerm hTermI hMI hGsumI hZeroI
      hTermNonneg hMzero hGHnonpos hZeroNonpos hItoJoint
  refine ⟨hBudget.1, hBudget.2.1, hBudget.2.2, ?_⟩
  exact avram_wave6_06_original_inclusive_random_clock_real_cash_budget_to_ennreal
    X x C D hD q τ Cash hCash hCashFinite
    hBudget.1 (w x) hBudget.2.2
