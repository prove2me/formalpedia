-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_discountedPayoff_zero_outside_rawTwoSidedExit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:06:32.986742+00:00
-- url     : https://prove2.me/submissions/a261c2db-0173-48f2-9b14-38ac5f14e287

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_upExit_before_controlledRuin_iff_rawExit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedPayoff_zero_outside_controlledUpExit
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Pathwise support of the stopped dividend reward on the raw successful
    two-sided exit event, including the no-exit and tie cases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x a : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω)
    (hraw : ¬
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) <
        (⨅ (s : ℝ≥0) (_ : X.X s ω < -x), (s : ℝ≥0∞))) :
    (∫⁻ t in paymentTimes (ruinTime X x (barrierStrategy X x a) ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0 := by
  apply barrierStrategy_discountedPayoff_zero_outside_controlledUpExit
    X q x a hx0 hxa ω
  intro hsuccess
  exact hraw
    ((barrierStrategy_upExit_before_controlledRuin_iff_rawExit
      X x a ha hx0 hxa ω).mp hsuccess)
