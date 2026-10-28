-- Prove2me | solution 1 for FeynmanKac.discount_zero_potential
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:13:42.119859+00:00
-- url     : https://prove2.me/submissions/4c612d45-9507-4dc6-b2b9-a569437c79e8

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

theorem solution (t s : ℝ) :
    Real.exp (-(∫ r in t..s, (0 : ℝ))) = 1 := by simp
