-- Prove2me | solution 1 for AvramDividend.Classical.capped_record_exponential_discount_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:34:23.751492+00:00
-- url     : https://prove2.me/submissions/5f68780b-d7cf-4938-9b0d-51fda313948a

import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-- The nonnegative exponential discount used at capped Lévy record times is measurable. -/
theorem solution (ε q : ℝ) :
    Measurable (fun t : ℝ≥0 =>
      ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))) := by
  fun_prop
