-- Prove2me | solution 1 for BookProof.ChapterGhostMajoranaRep.chi1_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:45:47.698981+00:00
-- url     : https://prove2.me/submissions/0a585411-157a-4ee9-b93a-86ca85c05791

-- Generated from ChapterGhostMajoranaRep.lean — solution of BookProof.ChapterGhostMajoranaRep.chi1_selfAdjoint
import Mathlib
import Definitions.Def_ChapterGhostMajoranaRep
open BookProof.ChapterGhostMajoranaRep





open Matrix BookProof.GhostField

set_option maxHeartbeats 1000000 in
theorem solution : chi1ᴴ = chi1 := by

  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chi1, psi, psiDag, Matrix.conjTranspose_apply]
