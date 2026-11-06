-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_cofinal_ito_budget_to_signed_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:59:06.170416+00:00
-- url     : https://prove2.me/submissions/f819b6d2-4d46-40c7-aebe-1e410cc72164

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_cofinal_original_ito_budget_implies_five_witness
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_five_source_witnesses_drop_nonintegrable_R_signed
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Cofinal actual-source stopped Ito budgets imply signed physical witnesses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (n : ℕ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ ω, (⨆ k : ℕ, S k ω) = ⊤)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (τk : ℕ → Ω → ℝ≥0)
    (hτk : ∀ k ω, τk k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal)
    (W Cash Term : Ω → ℝ)
    (Wk Cashk Termk : ℕ → Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hWk : ∀ k ω, Wk k ω =
      if τk k ω = 0 ∨ (τk k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τk k ω) ω - rightLimit D (τk k ω) ω
      else riskProcess X x D (τk k ω) ω)
    (hCashk : ∀ k ω, Cashk k ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τk k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    (hTermk : ∀ k ω, Termk k ω =
      Real.exp (-(q * (τk k ω : ℝ))) * w (Wk k ω))
    (hFmeas : ∀ k, Measurable (fun ω => Termk k ω + Cashk k ω))
    (hFint : ∀ k, Integrable (fun ω => Termk k ω + Cashk k ω) P)
    (hBudget : ∀ k, (∫ ω, Termk k ω + Cashk k ω ∂P) ≤ w x) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by
  have hFive :=
    avram_p4_f4_cofinal_original_ito_budget_implies_five_witness
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD q n S hSmono hSsup τ hτ τk hτk
      W Cash Term Wk Cashk Termk hW hCash hTerm hTermMeas hCashI
      hWk hCashk hTermk hFmeas hFint hBudget
  exact avram_p4_f3_five_source_witnesses_drop_nonintegrable_R_signed
    Term Cash (w x) hFive
