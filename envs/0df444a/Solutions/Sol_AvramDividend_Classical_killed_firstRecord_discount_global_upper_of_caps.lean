-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_discount_global_upper_of_caps
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:33:45.437841+00:00
-- url     : https://prove2.me/submissions/dd53639f-2b1c-4a19-840b-c98ec6d23d23

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_killed_weight_global_lintegral_le_of_uniform_caps
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b ε q : ℝ)
    (hT : Measurable (twoSidedExitUpTime X b))
    (hw : Measurable (fun ω : Ω =>
      if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp (-(q *
          (twoSidedExitUpTime X b ω).toReal))) else 0))
    (bound : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ ω, if twoSidedExitUpTime X b ω ≤ (n : ℝ≥0∞) then
        (if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp (-(q *
            (twoSidedExitUpTime X b ω).toReal))) else 0)
        else 0 ∂P) ≤ bound) :
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp (-(q *
        (twoSidedExitUpTime X b ω).toReal))) else 0 ∂P) ≤ bound := by 
  refine killed_weight_global_lintegral_le_of_uniform_caps P (twoSidedExitUpTime X b) hT _ hw ?_ bound hbound
  intro ω hω
  rw [if_neg]
  rw [hω]; exact not_top_lt
