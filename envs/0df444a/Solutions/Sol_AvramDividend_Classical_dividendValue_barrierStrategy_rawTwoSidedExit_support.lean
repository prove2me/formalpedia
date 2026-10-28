-- Prove2me | solution 1 for AvramDividend.Classical.dividendValue_barrierStrategy_rawTwoSidedExit_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:30:52.198727+00:00
-- url     : https://prove2.me/submissions/b5e9e3f7-2e99-46ab-ba46-36159856dc23

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedPayoff_zero_outside_rawTwoSidedExit
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Only paths with successful raw upper-before-lower passage can pay
    dividends under the stopped barrier strategy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x a : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      ∫⁻ ω, if (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) <
          (⨅ (s : ℝ≥0) (_ : X.X s ω < -x), (s : ℝ≥0∞)) then
        (∫⁻ t in paymentTimes (ruinTime X x (barrierStrategy X x a) ω),
          ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X x a) ω)) else 0 ∂P := by
  classical
  unfold dividendValue
  apply lintegral_congr
  intro ω
  by_cases hraw :
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) <
        (⨅ (s : ℝ≥0) (_ : X.X s ω < -x), (s : ℝ≥0∞))
  · simp only [hraw, ite_true]
  · simp only [hraw, ite_false]
    exact barrierStrategy_discountedPayoff_zero_outside_rawTwoSidedExit
      X q x a ha hx0 hxa ω hraw
