-- Prove2me | solution 1 for AvramDividend.Classical.chat04_positive_discount_exponential_halfline_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:47:13.848927+00:00
-- url     : https://prove2.me/submissions/b150d517-8ec3-47e9-864b-15b788549207

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith

open MeasureTheory Set
theorem solution (p : ℝ) (hp : 0 < p) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t))) = 1 / p := by 
  have h := integral_exp_mul_Ioi (a := -p) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, zero_sub] at h
  have e : (fun t : ℝ => Real.exp (-(p * t))) = fun t => Real.exp (-p * t) := by
    ext t; ring_nf
  rw [e, h]; field_simp
