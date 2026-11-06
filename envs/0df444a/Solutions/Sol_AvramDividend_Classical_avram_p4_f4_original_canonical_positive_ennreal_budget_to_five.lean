-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_original_canonical_positive_ennreal_budget_to_five
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:01:25.658211+00:00
-- url     : https://prove2.me/submissions/998c6175-5fde-467c-92c8-d51c47a63c17

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_cash_nonnegative_from_dividend_measure
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_stopped_terminal_L1_of_combined_ennreal_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_five_witness_iff_expected_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Canonical same-process terminal/cash hypotheses reduce five-component
source verification to one independently proved ENNReal expected payoff bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hBudget : (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x)) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hwx : 0 ≤ w x :=
    avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
      w C hw0 hw_cont hw_smooth hw_grad x (le_of_lt hx) hxc
  have hTermNN : ∀ ω, 0 ≤ Term ω :=
    avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hxc
      D hD q τ W Term hW hTerm
  have hCashNN : ∀ ω, 0 ≤ Cash ω :=
    avram_p4_f_assembly_original_stopped_cash_nonnegative_from_dividend_measure
      X q x D τ Cash hCash
  obtain ⟨hTermI, hRealBudget⟩ :=
    avram_p4_f4_stopped_terminal_L1_of_combined_ennreal_budget
      P Term Cash hTermMeas (Filter.Eventually.of_forall hTermNN)
      hCashI (Filter.Eventually.of_forall hCashNN)
      (w x) hwx hBudget
  exact (avram_p4_f4_five_witness_iff_expected_budget
    Term Cash hTermI hCashI (w x)).mp hRealBudget
