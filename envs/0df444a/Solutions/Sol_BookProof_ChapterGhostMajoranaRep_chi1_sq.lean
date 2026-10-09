-- Prove2me | solution 1 for BookProof.ChapterGhostMajoranaRep.chi1_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:46:01.51659+00:00
-- url     : https://prove2.me/submissions/fdfb34d8-5314-4fc5-b4d6-e7ca7a1e7e62

-- Generated from ChapterGhostMajoranaRep.lean — solution of BookProof.ChapterGhostMajoranaRep.chi1_sq
import Mathlib
import Definitions.Def_ChapterGhostMajoranaRep
open BookProof.ChapterGhostMajoranaRep





open Matrix BookProof.GhostField

set_option maxHeartbeats 1000000 in
theorem solution : chi1 * chi1 = 1 := by

  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chi1, psi, psiDag, Matrix.mul_apply, Fin.sum_univ_two]
