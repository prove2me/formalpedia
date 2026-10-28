-- Prove2me | solution 1 for FeynmanKac.discount_at_start
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:32:16.312501+00:00
-- url     : https://prove2.me/submissions/f247c26b-88b8-440e-95e4-0ee8749a2fa7

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exponential discount over a zero-length interval equals one. -/
theorem solution {Ω : Type*} (X : ℝ → Ω → ℝ) (V : ℝ → ℝ → ℝ)
    (t : ℝ) (ω : Ω) :
    Real.exp (-(∫ r in t..t, V (X r ω) r)) = 1 := by
  calc
    Real.exp (-(∫ r in t..t, V (X r ω) r)) = Real.exp 0 := by
      simp only [intervalIntegral.integral_same, neg_zero]
    _ = 1 := Real.exp_zero
