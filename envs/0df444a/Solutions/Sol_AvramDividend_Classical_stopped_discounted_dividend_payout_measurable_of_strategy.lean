-- Prove2me | solution 1 for AvramDividend.Classical.stopped_discounted_dividend_payout_measurable_of_strategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:55:37.084987+00:00
-- url     : https://prove2.me/submissions/51706afe-1225-421e-81e0-339061bfa243

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_dividend_payout_eq_iSup_unit_cash_toReal_of_strategy
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_real_cash_prefix_measurable_of_strategy
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exact capped, stopped Stieltjes payout is a measurable random
    variable for any real finite horizon, including dividend jump atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  have hPrefix := stopped_discounted_real_cash_prefix_measurable_of_strategy
    X q x D hD T
  have hSup : Measurable (fun ω : Ω =>
      ⨆ n : ℕ, ENNReal.ofReal
        (∑ k ∈ Finset.range n,
          (∫⁻ t in
            (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
              Ico (k : ℝ) ((k : ℝ) + 1),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)) :=
    Measurable.iSup hPrefix
  have hEq :
      (fun ω : Ω =>
        ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (fun ω : Ω =>
        ⨆ n : ℕ, ENNReal.ofReal
          (∑ k ∈ Finset.range n,
            (∫⁻ t in
              (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
                Ico (k : ℝ) ((k : ℝ) + 1),
              ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)) := by
    funext ω
    exact stopped_discounted_dividend_payout_eq_iSup_unit_cash_toReal_of_strategy
      D hD q hq (ruinTime X x D ω) T ω
  rw [hEq]
  exact hSup
