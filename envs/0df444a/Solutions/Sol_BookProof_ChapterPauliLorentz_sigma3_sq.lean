-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.sigma3_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:06:41.321088+00:00
-- url     : https://prove2.me/submissions/3696e98d-0cb0-45be-b1eb-b7f99a50722a

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.sigma3_sq
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution : σ3 * σ3 = 1 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3, Matrix.mul_apply, Fin.sum_univ_two]
