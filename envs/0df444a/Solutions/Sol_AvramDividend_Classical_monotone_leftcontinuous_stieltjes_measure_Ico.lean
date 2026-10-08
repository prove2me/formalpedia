-- Prove2me | solution 1 for AvramDividend.Classical.monotone_leftcontinuous_stieltjes_measure_Ico
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:17:24.493068+00:00
-- url     : https://prove2.me/submissions/01dde8fc-72f3-47e5-bf3a-a463ba2dc0d5

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (f : ℝ → ℝ) (hf : Monotone f)
    (hleft : ∀ t : ℝ, ContinuousWithinAt f (Iic t) t)
    (a b : ℝ) :
    hf.stieltjesFunction.measure (Ico a b) =
      ENNReal.ofReal (f b - f a) := by
  have hLim (t : ℝ) :
      Function.leftLim (hf.stieltjesFunction : ℝ → ℝ) t = f t := by
    change Function.leftLim (Function.rightLim f) t = f t
    rw [leftLim_rightLim (hf.tendsto_leftLim t)]
    exact (hleft t).leftLim_eq
  rw [hf.stieltjesFunction.measure_Ico, hLim b, hLim a]
