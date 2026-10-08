-- Prove2me | solution 1 for BookProof.SpinStatistics.fermiCreate1_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T10:46:57.169761+00:00
-- url     : https://prove2.me/submissions/ec1ba158-b5eb-48a9-8dbc-e09bc4c5ac18

import Mathlib
import Definitions.Def_ChapterSpinStatistics

open BookProof.SpinStatistics Matrix

theorem solution : fermiCreate1 * fermiCreate1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fermiCreate1, fermiCreate2, fermiAnnih1, fermiAnnih2, fermiNumber1, fermiNumber2,
      conjTranspose_apply, mul_apply, Matrix.add_apply, Fin.sum_univ_four, of_apply,
      cons_val_zero, cons_val_succ, cons_val_one, cons_val_two, one_apply,
      star_zero, star_one]

