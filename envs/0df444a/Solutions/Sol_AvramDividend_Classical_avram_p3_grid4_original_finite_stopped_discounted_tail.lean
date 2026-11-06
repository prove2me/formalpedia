-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_finite_stopped_discounted_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:35:10.075209+00:00
-- url     : https://prove2.me/submissions/0d963f39-61b5-40f8-9c82-3620a78499bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every original ruin/horizon-clamped tail lies inside the finite closed-horizon Stieltjes mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (τ T δ : ℝ≥0) (hτT : τ ≤ T)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ s in paymentTimes σ ∩ Ioc ((τ - δ : ℝ≥0) : ℝ) (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤ := by
  have hBound : (τ : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hτT
  have hSubset :
      paymentTimes σ ∩ Ioc ((τ - δ : ℝ≥0) : ℝ) (τ : ℝ) ⊆
      paymentTimes σ ∩ Iic (T : ℝ) := by
    intro s hs
    exact ⟨hs.1, le_trans hs.2.2 hBound⟩
  exact lt_of_le_of_lt (lintegral_mono_set hSubset)
    (avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
      D hD ω σ T q hq)
