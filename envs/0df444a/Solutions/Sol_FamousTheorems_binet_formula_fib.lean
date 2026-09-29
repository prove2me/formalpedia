-- Prove2me | solution 1 for FamousTheorems.binet_formula_fib
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:08:36.730321+00:00
-- url     : https://prove2.me/submissions/6772ca71-bd8d-4bb4-b4c2-8be482b6a6a3

import Mathlib

theorem solution (n : ℕ) :
    (Nat.fib n : ℝ) = (Real.goldenRatio ^ n - Real.goldenConj ^ n) / Real.sqrt 5 :=
  Real.coe_fib_eq n
