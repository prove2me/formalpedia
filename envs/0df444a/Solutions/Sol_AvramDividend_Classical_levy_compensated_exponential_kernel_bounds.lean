-- Prove2me | solution 1 for AvramDividend.Classical.levy_compensated_exponential_kernel_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:06:28.109437+00:00
-- url     : https://prove2.me/submissions/31cf0709-d04b-49e7-a332-ee1b4cd53fde

import Mathlib.Analysis.Complex.Exponential
theorem solution (θ t : ℝ) (hθ : 0 ≤ θ) (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-θ * t) ∧
      1 - Real.exp (-θ * t) ≤ θ * t := by
  have hprod : 0 ≤ θ * t := mul_nonneg hθ ht
  constructor
  · apply sub_nonneg.mpr
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · have h := Real.add_one_le_exp (-(θ * t))
    have he : Real.exp (-θ * t) = Real.exp (-(θ * t)) := by
      congr 1
      ring
    rw [he]
    nlinarith
