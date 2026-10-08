-- Prove2me | solution 1 for BookProof.SpinStatistics.fermi_CAR1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T10:49:57.059596+00:00
-- url     : https://prove2.me/submissions/6317ff84-4139-4ef3-9bb4-ff4e3167a5ec

import Mathlib
import Definitions.Def_ChapterSpinStatistics

open BookProof.SpinStatistics Matrix

theorem solution : fermiAnnih1 * fermiCreate1 + fermiCreate1 * fermiAnnih1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fermiCreate1, fermiCreate2, fermiAnnih1, fermiAnnih2, fermiNumber1, fermiNumber2,
      conjTranspose_apply, mul_apply, Matrix.add_apply, Fin.sum_univ_four, of_apply, Matrix.vecMul_apply_eq_sum,
      cons_val_zero, cons_val_succ, cons_val_one, cons_val_two, one_apply,
      star_zero, star_one]

