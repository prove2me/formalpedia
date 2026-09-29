-- Prove2me | solution 2 for ErlerGross.B3_double_integral_eval
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T16:31:34.242831+00:00
-- url     : https://prove2.me/submissions/0fac6f19-0ea5-482a-892c-b6d7d758a93d

import Theorems.Thm_ErlerGross_B3_double_integral_eq_tsum
import Theorems.Thm_ErlerGross_B3_rational_tsum_eval

open Real Filter Topology MeasureTheory ErlerGross

theorem solution :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      (1 - y) / (1 - x ^ 2 * y ^ 3)) = Real.log (27 / 16) := by
  exact ErlerGross.B3_double_integral_eq_tsum.trans ErlerGross.B3_rational_tsum_eval
