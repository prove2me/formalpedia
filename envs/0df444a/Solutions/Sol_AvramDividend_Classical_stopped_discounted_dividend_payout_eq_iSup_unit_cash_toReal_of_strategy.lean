-- Prove2me | solution 1 for AvramDividend.Classical.stopped_discounted_dividend_payout_eq_iSup_unit_cash_toReal_of_strategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:20:35.538747+00:00
-- url     : https://prove2.me/submissions/d91fef6e-dfe1-45ea-81d1-3fc7e3b34c8d

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_dividend_payout_eq_iSup_real_unit_cash
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_unit_cash_ne_top_of_strategy
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Actual stopped Stieltjes dividend payouts are suprema of finite real cash
    sums, retaining continuous dividends and right-jump atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ⨆ n : ℕ, ENNReal.ofReal
        (∑ k ∈ Finset.range n,
          (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩
            Ico (k : ℝ) ((k : ℝ) + 1),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) := by
  let cash : ℕ → ℝ := fun k =>
    (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩
      Ico (k : ℝ) ((k : ℝ) + 1),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  have hCashNN : ∀ k : ℕ, 0 ≤ cash k := by
    intro k
    exact ENNReal.toReal_nonneg
  have hCashEq : ∀ k : ℕ,
      ENNReal.ofReal (cash k) =
        ∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩
          Ico (k : ℝ) ((k : ℝ) + 1),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) := by
    intro k
    exact ENNReal.ofReal_toReal
      (AvramDividend.Classical.stopped_discounted_unit_cash_ne_top_of_strategy
        D hD q hq σ T ω k)
  change (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ⨆ n : ℕ, ENNReal.ofReal (∑ k ∈ Finset.range n, cash k)
  exact AvramDividend.Classical.stopped_discounted_dividend_payout_eq_iSup_real_unit_cash
    D σ (T : ℝ) q ω cash hCashNN hCashEq
