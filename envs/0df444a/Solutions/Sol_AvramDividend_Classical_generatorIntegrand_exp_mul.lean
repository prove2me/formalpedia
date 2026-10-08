-- Prove2me | solution 1 for AvramDividend.Classical.generatorIntegrand_exp_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:30:41.450727+00:00
-- url     : https://prove2.me/submissions/8e0a6fb9-490e-4c1a-b84b-a1b90de7052f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

theorem solution
    (θ x y : ℝ) :
    SpectrallyNegativeLevy.generatorIntegrand (fun z : ℝ => Real.exp (θ * z)) x y =
      Real.exp (θ * x) *
        (Real.exp (θ * y) - 1 -
          θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) := by
  have hd : deriv (fun z : ℝ => Real.exp (θ * z)) x =
      θ * Real.exp (θ * x) := by
    have h := congrFun (iteratedDeriv_exp_const_mul 1 θ) x
    simpa using h
  unfold SpectrallyNegativeLevy.generatorIntegrand
  rw [hd]
  change Real.exp (θ * (x + y)) - Real.exp (θ * x) -
      (θ * Real.exp (θ * x)) * y * (Ioo (-1 : ℝ) 1).indicator 1 y =
    Real.exp (θ * x) *
      (Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
  rw [mul_add, Real.exp_add]
  ring
