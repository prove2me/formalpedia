-- Prove2me | solution 1 for BookProof.GhostField.numberOp_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:40:05.459382+00:00
-- url     : https://prove2.me/submissions/6afdf36a-a5bd-4352-a4db-2e7207ba62e2

-- Generated from ChapterGhostField.lean — solution of BookProof.GhostField.numberOp_eq
import Mathlib
import Definitions.Def_ChapterGhostField
open BookProof.GhostField











open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : numberOp = !![1, 0; 0, 0] := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [numberOp, psi, psiDag, Matrix.mul_apply, Fin.sum_univ_two]
