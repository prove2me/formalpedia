-- Prove2me | solution 1 for BookProof.GhostField.numberOp_add_hole
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:38:23.746507+00:00
-- url     : https://prove2.me/submissions/2d60913a-e2b1-4a3b-8078-fcd89dab86a6

-- Generated from ChapterGhostField.lean — solution of BookProof.GhostField.numberOp_add_hole
import Mathlib
import Definitions.Def_ChapterGhostField
open BookProof.GhostField











open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : numberOp + psi * psiDag = 1 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [numberOp, psi, psiDag]
