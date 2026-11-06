-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_original_hjb_preflight_residual_all_cap_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:36:49.359622+00:00
-- url     : https://prove2.me/submissions/a8a3ebb7-4574-4cf2-8334-d49be97373bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_original_bv_ubv_nonnegative_clock_cash_hjb_preflight
import Theorems.Thm_AvramDividend_Classical_avram_limit1_original_uniform_source_to_full_dividendValue_bv_ubv
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_implies_components
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Canonical original stopped clocks, postpayment W/Cash/Term and cash
    integrability are preflight facts. Only the genuine stochastic residual
    remains as a source obligation for all BV/UBV capped and top values. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (hResidual : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ k : ℕ, 0 < k →
      ∀ (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ),
      (∀ ω, τ ω =
        (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal) →
      (∀ ω, W ω = if τ ω = 0 ∨
        (τ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω) →
      (∀ ω, Cash ω = (∫⁻ s in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) →
      (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) →
      ∃ M G H : Ω → ℝ,
        Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
        (∫ ω, M ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
        (∀ᵐ ω ∂P, Term ω + Cash ω ≤
          w x + M ω + G ω + H ω)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  apply local_verification_from_uniform_strategy_bound X q w C
  intro x hx hxC D hD
  apply avram_limit1_original_uniform_source_to_full_dividendValue_bv_ubv
    X q hq w C hC hw0 hw_cont hw_neg hw_smooth
    (fun y hy hyC => (local_verification_hjb_implies_components
      X q w C hw_hjb y hy hyC).2.2) x hx hxC D hD
  intro k hk
  obtain ⟨τ, hτeq, hτMeas, hτStop, W, Cash, Term,
    hW, hCash, hTerm, hTermMeas, hCashI,
    hGen, hGrad, hNonneg, hJump⟩ :=
    avram_limit1_original_bv_ubv_nonnegative_clock_cash_hjb_preflight
      X q w C hC hw0 hw_cont hw_neg hw_smooth hw_hjb
      x hx hxC D hD k
  exact ⟨τ, W, Cash, Term, hτeq, hτMeas, hW, hCash, hTerm,
    hCashI,
    hResidual x hx hxC D hD k hk τ W Cash Term
      hτeq hW hCash hTerm⟩
