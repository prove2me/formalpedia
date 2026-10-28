-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_resolvent_double_discount_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:35:31.551279+00:00
-- url     : https://prove2.me/submissions/f7a7dfce-7cef-458a-a91b-b00e186dfa82

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Set

theorem solution
    (p q : ℝ) (f : ℝ → ℝ) :
    (∫ t in Ioi (0 : ℝ),
      Real.exp (-(p * t)) * (Real.exp (-(q * t)) * f t)) =
    (∫ t in Ioi (0 : ℝ), Real.exp (-((p + q) * t)) * f t) := by 
  congr 1
  funext t
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf
