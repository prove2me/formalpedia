-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_original_bv_all_ubv_positive_residual_to_all_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:30:42.121144+00:00
-- url     : https://prove2.me/submissions/95329404-0b79-4cdb-85b3-360a4c3dec56

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_original_bv_ubv_nonnegative_clock_cash_hjb_preflight
import Theorems.Thm_AvramDividend_Classical_avram_limit1_original_uniform_source_to_full_dividendValue_bv_ubv
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_implies_components
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound
import Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_zero_actual_dividendValue_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Original BV cash residuals at all reserves plus UBV positive-reserve
    residuals suffice. The UBV zero-reserve branch uses its proved atom law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (hResidual : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      (X.BoundedVariation ∨ 0 < x) →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ k : ℕ, 0 < k →
      ∀ (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ),
      (∀ ω, τ ω = (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal) →
      (∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω) →
      (∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) →
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
  have hValue : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      (X.BoundedVariation ∨ 0 < x) → ∀ D : ℝ≥0 → Ω → ℝ,
      IsAdmissibleLe X x C D → dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
    intro x hx hxC hxBranch D hD
    apply avram_limit1_original_uniform_source_to_full_dividendValue_bv_ubv
      X q hq w C hC hw0 hw_cont hw_neg hw_smooth
      (fun y hy hyC =>
        (local_verification_hjb_implies_components
          X q w C hw_hjb y hy hyC).2.2)
      x hx hxC D hD
    intro k hk
    obtain ⟨τ, hτeq, hτMeas, hτStop, W, Cash, Term, hW, hCash, hTerm,
      hTermMeas, hCashI, hGen, hGrad, hNonneg, hJump⟩ :=
      avram_limit1_original_bv_ubv_nonnegative_clock_cash_hjb_preflight
        X q w C hC hw0 hw_cont hw_neg hw_smooth hw_hjb
        x hx hxC D hD k
    exact ⟨τ, W, Cash, Term, hτeq, hτMeas, hW, hCash, hTerm, hCashI,
      hResidual x hx hxC hxBranch D hD k hk τ W Cash Term hτeq hW hCash hTerm⟩
  apply local_verification_from_uniform_strategy_bound X q w C
  intro x hx hxC D hD
  by_cases hxpos : 0 < x
  · exact hValue x hx hxC (Or.inr hxpos) D hD
  have hx0 : x = 0 := le_antisymm (le_of_not_gt hxpos) hx
  subst x
  by_cases hBV : X.BoundedVariation
  · exact hValue 0 (by norm_num) hxC (Or.inl hBV) D hD
  · exact avram_limit1_ubv_zero_actual_dividendValue_le
      X hBV q w C hw0 hw_cont (hw_smooth.1 hBV)
      (fun y hy hyC => (local_verification_hjb_implies_components
        X q w C hw_hjb y hy hyC).2.2) D hD
