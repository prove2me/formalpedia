-- Prove2me | solution 1 for AvramDividend.Classical.chat03_discounted_upperfirst_lintegral_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:28:36.121963+00:00
-- url     : https://prove2.me/submissions/f12e59a7-4d63-467e-a3a3-bd5aabccc46a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_upperfirst_weight_le_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal

/-!
A probability-weighted upper-first discounted payoff has
finite ENNReal expectation bounded above by one.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (q : ℝ) (hq : 0 ≤ q) (up down : Ω → ℝ≥0∞) :
    (∫⁻ ω : Ω,
      if up ω < down ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (up ω))))
      else 0 ∂P) ≤ 1 := by
  calc
    (∫⁻ ω : Ω,
      if up ω < down ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (up ω))))
      else 0 ∂P) ≤ ∫⁻ (_ : Ω), (1 : ℝ≥0∞) ∂P :=
        lintegral_mono (fun ω =>
          chat03_discounted_upperfirst_weight_le_one q hq (up ω) (down ω))
    _ = 1 := by simp
