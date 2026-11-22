-- Prove2me | solution 2 for BroughanRH.moebius
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:13.130904+00:00
-- url     : https://prove2.me/submissions/bff19e15-c33b-48e3-a358-7944152c441b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis

theorem solution :
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) :=
  moebius_summatory_rpow_bound_of_riemannHypothesis mathlib_riemannHypothesis
