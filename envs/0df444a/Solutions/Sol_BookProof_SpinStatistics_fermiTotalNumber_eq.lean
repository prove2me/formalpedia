-- Prove2me | solution 1 for BookProof.SpinStatistics.fermiTotalNumber_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T12:39:47.387646+00:00
-- url     : https://prove2.me/submissions/8159afca-1c41-472e-9d77-cca3fea66fc5

-- Generated from ChapterSpinStatistics.lean — theorem BookProof.SpinStatistics.fermiTotalNumber_eq
import Mathlib
import Definitions.Def_ChapterSpinStatistics
open BookProof.SpinStatistics



open Matrix
open BookProof.SpinStatistics

theorem solution:
    fermiNumber1 + fermiNumber2 = !![0,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fermiNumber1, fermiNumber2, fermiCreate1, fermiCreate2, fermiAnnih1, fermiAnnih2, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
