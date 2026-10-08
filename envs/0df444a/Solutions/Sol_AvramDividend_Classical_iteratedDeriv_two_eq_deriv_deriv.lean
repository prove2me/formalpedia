-- Prove2me | solution 1 for AvramDividend.Classical.iteratedDeriv_two_eq_deriv_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:12:52.530461+00:00
-- url     : https://prove2.me/submissions/eaf8764f-6622-43e9-8471-7b6dae64d56f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (W : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv 2 W x = deriv (deriv W) x := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    iteratedDeriv_succ, iteratedDeriv_one]
