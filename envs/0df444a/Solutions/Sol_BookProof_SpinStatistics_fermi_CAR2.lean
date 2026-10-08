-- Prove2me | solution 1 for BookProof.SpinStatistics.fermi_CAR2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T10:49:57.701951+00:00
-- url     : https://prove2.me/submissions/7a234bc3-c8a0-4593-a6f9-2602a344522f

import Mathlib
import Definitions.Def_ChapterSpinStatistics

open BookProof.SpinStatistics Matrix

theorem solution : fermiAnnih2 * fermiCreate2 + fermiCreate2 * fermiAnnih2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fermiCreate1, fermiCreate2, fermiAnnih1, fermiAnnih2, fermiNumber1, fermiNumber2,
      conjTranspose_apply, mul_apply, Matrix.add_apply, Fin.sum_univ_four, of_apply, Matrix.vecMul_apply_eq_sum,
      cons_val_zero, cons_val_succ, cons_val_one, cons_val_two, one_apply,
      star_zero, star_one]

