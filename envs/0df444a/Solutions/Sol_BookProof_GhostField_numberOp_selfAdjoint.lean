-- Prove2me | solution 1 for BookProof.GhostField.numberOp_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:43:22.775971+00:00
-- url     : https://prove2.me/submissions/0f483df1-567a-4ae6-9246-12ff05270bee

-- Generated from ChapterGhostField.lean — solution of BookProof.GhostField.numberOp_selfAdjoint
import Mathlib
import Definitions.Def_ChapterGhostField
open BookProof.GhostField











open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : numberOp = numberOpᴴ := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [numberOp, psi, psiDag, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]
