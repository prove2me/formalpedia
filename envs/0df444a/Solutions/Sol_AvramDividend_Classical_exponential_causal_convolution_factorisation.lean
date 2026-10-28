-- Prove2me | solution 1 for AvramDividend.Classical.exponential_causal_convolution_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:07:39.441107+00:00
-- url     : https://prove2.me/submissions/9c3f5bfd-06e1-4dee-9c2d-1372a99f58c2

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open AvramDividend.Classical MeasureTheory Set

theorem solution
    (f g : ℝ → ℝ) (θ x : ℝ) :
    Real.exp (-(θ * x)) *
      (∫ s in Ioc (0 : ℝ) x, f (x - s) * g s ∂volume) =
    ∫ s in Ioc (0 : ℝ) x,
      (Real.exp (-(θ * (x - s))) * f (x - s)) *
        (Real.exp (-(θ * s)) * g s) ∂volume := by
  rw [← integral_const_mul]
  congr 1; ext s
  have : Real.exp (-(θ * x)) = Real.exp (-(θ * (x - s))) * Real.exp (-(θ * s)) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]; ring
