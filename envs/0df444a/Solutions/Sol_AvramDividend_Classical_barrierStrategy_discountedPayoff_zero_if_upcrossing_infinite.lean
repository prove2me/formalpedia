-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_discountedPayoff_zero_if_upcrossing_infinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:55:54.425517+00:00
-- url     : https://prove2.me/submissions/a5c54795-6c8b-4d40-8c77-a5cdcd076ef2

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_if_firstUpcrossing_infinite
import Theorems.Thm_AvramDividend_Classical_zeroCumulativeDividend_implies_zeroStieltjesPayoff
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Nonarrival at the barrier kills the entire discounted dividend
    payoff, including any infinite ruin-time scenario. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω)
    (hnever : (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω),
      (s : ℝ≥0∞)) = ⊤) :
    (∫⁻ t in paymentTimes
        (ruinTime X x (barrierStrategy X x a) ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0 := by
  exact zeroCumulativeDividend_implies_zeroStieltjesPayoff X q x
    (barrierStrategy X x a)
    (barrierStrategy_isDividendStrategy_nonnegative_barrier
      X x a hx0 (le_trans hx0 hxa))
    ω (barrierStrategy_zero_if_firstUpcrossing_infinite X x a ω hnever)