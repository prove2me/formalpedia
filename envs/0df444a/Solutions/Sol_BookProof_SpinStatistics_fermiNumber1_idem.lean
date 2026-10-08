-- Prove2me | solution 1 for BookProof.SpinStatistics.fermiNumber1_idem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T10:47:00.0021+00:00
-- url     : https://prove2.me/submissions/71b387f6-b386-40e8-887f-c8d16270e38e

import Mathlib
import Definitions.Def_ChapterSpinStatistics

open BookProof.SpinStatistics Matrix

theorem solution : fermiNumber1 * fermiNumber1 = fermiNumber1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fermiCreate1, fermiCreate2, fermiAnnih1, fermiAnnih2, fermiNumber1, fermiNumber2,
      conjTranspose_apply, mul_apply, Matrix.add_apply, Fin.sum_univ_four, of_apply,
      cons_val_zero, cons_val_succ, cons_val_one, cons_val_two, one_apply,
      star_zero, star_one]

