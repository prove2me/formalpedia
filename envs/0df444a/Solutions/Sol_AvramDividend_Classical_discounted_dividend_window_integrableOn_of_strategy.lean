-- Prove2me | solution 1 for AvramDividend.Classical.discounted_dividend_window_integrableOn_of_strategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:19:25.304405+00:00
-- url     : https://prove2.me/submissions/de16895b-91a4-41e4-bb33-cc5c32faa4ae

import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_integrableOn_of_finite_measure
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_paymentWindow_finite_of_strategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual finite-horizon stopped dividend payments admit a real-valued,
    absolutely integrable exponential Stieltjes discount factor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω) :
    IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω) := by
  apply discounted_stieltjes_integrableOn_of_finite_measure q hq
    (dividendMeasure D ω) (paymentTimes σ ∩ Iic (T : ℝ))
  · exact (paymentTimes_measurable σ).inter measurableSet_Iic
  · intro t ht
    exact ht.1.1
  · exact dividendMeasure_paymentWindow_finite_of_strategy D hD ω σ T
