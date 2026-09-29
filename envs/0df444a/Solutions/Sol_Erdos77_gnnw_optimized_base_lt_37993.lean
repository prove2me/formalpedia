-- Prove2me | solution 1 for Erdos77.gnnw_optimized_base_lt_37993
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:02:39.155262+00:00
-- url     : https://prove2.me/submissions/0bbb2149-fa55-492d-9fc2-23bcb9380bb6

import Mathlib

theorem solution :
    4 * Real.exp (- (0.14 : Real) / Real.exp 1) < (3.7993 : Real) := by
  let x : Real := (0.14 : Real) / Real.exp 1
  have hx : (103 : Real) / 2000 < x := by
    dsimp [x]
    rw [lt_div_iff₀ (Real.exp_pos 1)]
    nlinarith [Real.exp_one_lt_d9]
  have hsmall :
      (1 + (103 : Real) / 256000 : Real) ^ 128 < Real.exp x := by
    calc
      (1 + (103 : Real) / 256000 : Real) ^ 128 <
          (Real.exp (x / 128)) ^ 128 := by
        have hstep := Real.add_one_lt_exp (ne_of_gt (by positivity : 0 < x / 128))
        have hbase : 1 + (103 : Real) / 256000 < Real.exp (x / 128) := by
          nlinarith [hx, hstep]
        gcongr
      _ = Real.exp x := by
        calc
          (Real.exp (x / 128)) ^ 128 =
              Real.exp ((128 : Nat) * (x / 128)) := by rw [Real.exp_nat_mul]
          _ = Real.exp x := by congr 1; ring
  have hnumeric :
      (4 : Real) / 3.7993 < (1 + (103 : Real) / 256000 : Real) ^ 128 := by
    norm_num
  have htarget : (4 : Real) / 3.7993 < Real.exp x := hnumeric.trans hsmall
  have harg : -(0.14 : Real) / Real.exp 1 = -x := by
    dsimp [x]
    ring
  rw [harg, Real.exp_neg]
  have hinv : (Real.exp x)⁻¹ < 3.7993 / 4 := by
    rw [← one_div]
    rw [div_lt_iff₀ (Real.exp_pos x)]
    nlinarith [htarget]
  nlinarith