-- Prove2me | solution 1 for AvramDividend.Classical.derivZeroPlus_top_iff_deriv_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:57:05.119144+00:00
-- url     : https://prove2.me/submissions/c6d3102a-44a1-4c02-b5c1-94d5dca28a73

import Theorems.Thm_AvramDividend_Classical_deriv_tendsto_atTop_of_derivZeroPlus_top
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_top_of_right_tendsto_atTop

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter Set

/-- The extended right-derivative liminf is infinite exactly at ordinary right divergence. -/
theorem solution
    (W : ℝ → ℝ) :
    derivZeroPlus W = ⊤ ↔
      Tendsto (fun y : ℝ => deriv W y)
        (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  constructor
  · intro h
    exact deriv_tendsto_atTop_of_derivZeroPlus_top W h
  · intro h
    exact derivZeroPlus_eq_top_of_right_tendsto_atTop W h
