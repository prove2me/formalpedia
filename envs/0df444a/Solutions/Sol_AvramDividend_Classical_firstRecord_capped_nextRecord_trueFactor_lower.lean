-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_capped_nextRecord_trueFactor_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:42:07.595013+00:00
-- url     : https://prove2.me/submissions/d3023351-140b-4fb5-bb06-c2808648a394

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_markov_nextRecord_integral_lower
import Theorems.Thm_AvramDividend_Classical_capped_record_exponential_discount_measurable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The capped next-record lower bound with a discharged discount measurability hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (N : ℝ≥0)
    :
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
         twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
       ENNReal.ofReal ε *
         ENNReal.ofReal (Real.exp (-(q *
           (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal) : ℝ))))
      else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
       ENNReal.ofReal (ε * Real.exp
         (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0 ∂P) := by
  exact firstRecord_capped_markov_nextRecord_integral_lower
    X a b ε q ha hb hε N
    (capped_record_exponential_discount_measurable ε q)
