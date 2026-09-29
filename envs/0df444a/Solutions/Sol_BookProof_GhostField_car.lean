-- Prove2me | solution 1 for BookProof.GhostField.car
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:37:14.427701+00:00
-- url     : https://prove2.me/submissions/213ee511-d452-437f-8c43-97e7b1fecc4d

-- Generated from ChapterGhostField.lean — solution of BookProof.GhostField.car
import Mathlib
import Definitions.Def_ChapterGhostField
open BookProof.GhostField











open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : psi * psiDag + psiDag * psi = 1 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [psi, psiDag]
