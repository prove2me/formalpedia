-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_finite_discount_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:24:51.377234+00:00
-- url     : https://prove2.me/submissions/d0fbd234-7316-4325-8c5b-9dcb6d5fb88a

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Basic

open MeasureTheory
open scoped NNReal ENNReal
theorem solution
    (q ε : ℝ) :
    Measurable (fun t : ℝ≥0 =>
      ENNReal.ofReal (ε * Real.exp (-(q * (t : ℝ))))) := by 
  exact ENNReal.measurable_ofReal.comp (measurable_const.mul
    (Real.continuous_exp.measurable.comp (measurable_const.mul NNReal.continuous_coe.measurable).neg))
