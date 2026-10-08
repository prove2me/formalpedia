-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.sigma1_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:05:15.180121+00:00
-- url     : https://prove2.me/submissions/54aa1cee-d7af-4c00-9857-32d40fe2c5ff

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.sigma1_sq
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution : σ1 * σ1 = 1 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ1, Matrix.mul_apply, Fin.sum_univ_two]
