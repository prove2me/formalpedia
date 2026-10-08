-- Prove2me | solution 1 for BookProof.SpinStatistics.fermiNumber1_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T10:47:01.408023+00:00
-- url     : https://prove2.me/submissions/afa79726-f743-4eac-b299-5da9d4229ea5

import Mathlib
import Definitions.Def_ChapterSpinStatistics

open BookProof.SpinStatistics Matrix

theorem solution : fermiNumber1 = !![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fermiCreate1, fermiCreate2, fermiAnnih1, fermiAnnih2, fermiNumber1, fermiNumber2,
      conjTranspose_apply, mul_apply, Matrix.add_apply, Fin.sum_univ_four, of_apply,
      cons_val_zero, cons_val_succ, cons_val_one, cons_val_two, one_apply,
      star_zero, star_one]

