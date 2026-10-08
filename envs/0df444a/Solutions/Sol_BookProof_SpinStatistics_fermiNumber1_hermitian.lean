-- Prove2me | solution 1 for BookProof.SpinStatistics.fermiNumber1_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T10:46:58.463361+00:00
-- url     : https://prove2.me/submissions/c0c6b5a7-783b-42bd-aa85-45f646893208

import Mathlib
import Definitions.Def_ChapterSpinStatistics

open BookProof.SpinStatistics Matrix

theorem solution : fermiNumber1ᴴ = fermiNumber1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fermiCreate1, fermiCreate2, fermiAnnih1, fermiAnnih2, fermiNumber1, fermiNumber2,
      conjTranspose_apply, mul_apply, Matrix.add_apply, Fin.sum_univ_four, of_apply,
      cons_val_zero, cons_val_succ, cons_val_one, cons_val_two, one_apply,
      star_zero, star_one]

