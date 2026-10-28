-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_capped_integral_eq_natTruncation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:34:03.136319+00:00
-- url     : https://prove2.me/submissions/8b8c0ac3-a97f-4bf7-b2a1-4dc3ad4807d8

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_discount_equals_uncapped_on_horizon
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The capped first-record integral is the ordinary truncation of the uncapped killed reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (hε : 0 ≤ ε) (N : ℝ≥0) :
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
       ENNReal.ofReal ε *
         ENNReal.ofReal (Real.exp (-(q *
           (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal) : ℝ))))
      else 0 ∂P) =
    (∫⁻ ω, if twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      (if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X b ω).toReal)))
       else 0) else 0 ∂P) := by
  apply lintegral_congr
  intro ω
  by_cases hN : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)
  · by_cases hR : twoSidedExitUpTime X b ω < barrierRuinTime X a ω
    · have hB : twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
          twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) := ⟨hR, hN⟩
      simp only [if_pos hB, if_pos hN, if_pos hR]
      rw [firstRecord_capped_discount_equals_uncapped_on_horizon
        X b ε q N ω hN]
      rw [ENNReal.ofReal_mul hε]
    · have hB : ¬ (twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
          twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)) := by
        intro h
        exact hR h.1
      simp only [if_neg hB, if_pos hN, if_neg hR]
  · have hB : ¬ (twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)) := by
      intro h
      exact hN h.2
    simp only [if_neg hB, if_neg hN]
