-- Prove2me | solution 1 for BookProof.GhostField.numberOp_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:41:51.755069+00:00
-- url     : https://prove2.me/submissions/977e6720-9e1b-4ebf-a6ec-22ca5949f5c7

-- Generated from ChapterGhostField.lean — solution of BookProof.GhostField.numberOp_idempotent
import Mathlib
import Definitions.Def_ChapterGhostField
open BookProof.GhostField











open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : numberOp * numberOp = numberOp := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [numberOp, psi, psiDag, Matrix.mul_apply, Fin.sum_univ_two]
