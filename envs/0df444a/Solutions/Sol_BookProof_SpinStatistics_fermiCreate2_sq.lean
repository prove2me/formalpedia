-- Prove2me | solution 1 for BookProof.SpinStatistics.fermiCreate2_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T10:46:57.84373+00:00
-- url     : https://prove2.me/submissions/82b5b123-892b-427c-8425-90ba4a7eb4ef

import Mathlib
import Definitions.Def_ChapterSpinStatistics

open BookProof.SpinStatistics Matrix

theorem solution : fermiCreate2 * fermiCreate2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fermiCreate1, fermiCreate2, fermiAnnih1, fermiAnnih2, fermiNumber1, fermiNumber2,
      conjTranspose_apply, mul_apply, Matrix.add_apply, Fin.sum_univ_four, of_apply,
      cons_val_zero, cons_val_succ, cons_val_one, cons_val_two, one_apply,
      star_zero, star_one]

