-- Prove2me | solution 1 for DirichletUnitTheorem.sum_mult_log_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:19:41.370727+00:00
-- url     : https://prove2.me/submissions/4c105087-edcf-4642-a7a7-44eaa8023128

import Mathlib
open NumberField

theorem solution (K : Type*) [Field K] [NumberField K] (u : (𝓞 K)ˣ) :
    ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K)) = 0 :=
  Units.sum_mult_mul_log u
