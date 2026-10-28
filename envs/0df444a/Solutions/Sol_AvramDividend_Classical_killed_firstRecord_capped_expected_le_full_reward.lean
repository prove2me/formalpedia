-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_capped_expected_le_full_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:05:03.32701+00:00
-- url     : https://prove2.me/submissions/9a878792-5a92-43c2-989f-862e79f6f77f

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A finite cap can only remove nonnegative discounted first-record payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (N : ℝ≥0) :
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
                  twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      ENNReal.ofReal ε *
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
      ENNReal.ofReal ε *
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P) := by
  apply lintegral_mono
  intro ω
  by_cases hcap :
      twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)
  · simp [hcap, hcap.1]
  · simp only [if_neg hcap]
    exact bot_le
