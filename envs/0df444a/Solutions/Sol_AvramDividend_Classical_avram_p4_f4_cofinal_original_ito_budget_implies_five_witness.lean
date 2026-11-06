-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_cofinal_original_ito_budget_implies_five_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:05:20.289206+00:00
-- url     : https://prove2.me/submissions/0b5f29b0-c62c-4d37-b900-afe99dcf5f33

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_cash_nonnegative_from_dividend_measure
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_cofinal_clock_payoff_eventually_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_local_fatou_to_original_five_witness
import Theorems.Thm_cofinal_ito_to_five_pointwise_upper_bound_99552064
import Theorems.Thm_cofinal_ito_to_five_identity_57c30a1d

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual original Lévy and dividend cofinal local budgets imply natural
five-witness dominance, with no natural-clock L1 martingale limit premise. -/
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
  have hTermNN : ∀ ω, 0 ≤ Term ω :=
    avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hxc
      D hD q τ W Term hW hTerm
  have hCashNN : ∀ ω, 0 ≤ Cash ω :=
    avram_p4_f_assembly_original_stopped_cash_nonnegative_from_dividend_measure
      X q x D τ Cash hCash
  have hFNN : ∀ k, 0 ≤ᵐ[P] (fun ω => Termk k ω + Cashk k ω) := cofinal_ito_to_five_pointwise_upper_bound_99552064 (Ω := Ω) (mΩ := mΩ) (P := P) (𝓕 := 𝓕) (X := X) (hBV := hBV) (w := w) (C := C) (hC := hC) (hw0 := hw0) (hw_cont := hw_cont) (hw_neg := hw_neg) (hw_smooth := hw_smooth) (hw_grad := hw_grad) (x := x) (hxc := hxc) (D := D) (hD := hD) (q := q) (n := n) (S := S) (hSmono := hSmono) (hSsup := hSsup) (τ := τ) (hτ := hτ) (τk := τk) (hτk := hτk) (W := W) (Cash := Cash) (Term := Term) (Wk := Wk) (Cashk := Cashk) (Termk := Termk) (hW := hW) (hCash := hCash) (hTerm := hTerm) (hTermMeas := hTermMeas) (hCashI := hCashI) (hWk := hWk) (hCashk := hCashk) (hTermk := hTermk) (hFmeas := hFmeas) (hFint := hFint) (hBudget := hBudget) (hTermNN := hTermNN) (hCashNN := hCashNN)
  have hb : 0 ≤ w x :=
    (integral_nonneg_of_ae (hFNN 0)).trans (hBudget 0)
  have hlim : ∀ ω, Tendsto
      (fun k => ENNReal.ofReal (Termk k ω + Cashk k ω)) atTop
      (𝓝 (ENNReal.ofReal (Term ω + Cash ω))) := cofinal_ito_to_five_identity_57c30a1d (Ω := Ω) (mΩ := mΩ) (P := P) (𝓕 := 𝓕) (X := X) (hBV := hBV) (w := w) (C := C) (hC := hC) (hw0 := hw0) (hw_cont := hw_cont) (hw_neg := hw_neg) (hw_smooth := hw_smooth) (hw_grad := hw_grad) (x := x) (hxc := hxc) (D := D) (hD := hD) (q := q) (n := n) (S := S) (hSmono := hSmono) (hSsup := hSsup) (τ := τ) (hτ := hτ) (τk := τk) (hτk := hτk) (W := W) (Cash := Cash) (Term := Term) (Wk := Wk) (Cashk := Cashk) (Termk := Termk) (hW := hW) (hCash := hCash) (hTerm := hTerm) (hTermMeas := hTermMeas) (hCashI := hCashI) (hWk := hWk) (hCashk := hCashk) (hTermk := hTermk) (hFmeas := hFmeas) (hFint := hFint) (hBudget := hBudget) (hTermNN := hTermNN) (hCashNN := hCashNN) (hFNN := hFNN) (hb := hb)
  exact avram_p4_f4_local_fatou_to_original_five_witness
    Term Cash hTermMeas hCashI
    (Filter.Eventually.of_forall hTermNN)
    (Filter.Eventually.of_forall hCashNN)
    (fun k ω => Termk k ω + Cashk k ω)
    hFmeas hFint hFNN hlim (w x) hb hBudget
