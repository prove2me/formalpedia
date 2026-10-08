-- Prove2me | solution 1 for BookProof.SpinStatistics.fermiNumber2_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T10:47:02.36647+00:00
-- url     : https://prove2.me/submissions/12bac7ad-4777-422e-84c2-8d9bc62c22c6

import Mathlib
import Definitions.Def_ChapterSpinStatistics

open BookProof.SpinStatistics Matrix

theorem solution : fermiNumber2 = !![0,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fermiCreate1, fermiCreate2, fermiAnnih1, fermiAnnih2, fermiNumber1, fermiNumber2,
      conjTranspose_apply, mul_apply, Matrix.add_apply, Fin.sum_univ_four, of_apply,
      cons_val_zero, cons_val_succ, cons_val_one, cons_val_two, one_apply,
      star_zero, star_one]

