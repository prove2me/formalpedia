-- Prove2me | solution 1 for BookProof.GhostField.psi_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:48:14.816587+00:00
-- url     : https://prove2.me/submissions/5c57b150-a825-4b35-92c1-ecf1d7466941

-- Generated from ChapterGhostField.lean — solution of BookProof.GhostField.psi_sq
import Mathlib
import Definitions.Def_ChapterGhostField
open BookProof.GhostField











open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : psi * psi = 0 := by

  ext i j; fin_cases i <;> fin_cases j <;> simp [psi, Matrix.mul_apply, Fin.sum_univ_two]
