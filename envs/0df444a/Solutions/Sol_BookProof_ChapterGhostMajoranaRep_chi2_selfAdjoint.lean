-- Prove2me | solution 1 for BookProof.ChapterGhostMajoranaRep.chi2_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:45:48.665867+00:00
-- url     : https://prove2.me/submissions/cc2c03f2-7fdc-4e12-88f8-3aa199c8d7ab

-- Generated from ChapterGhostMajoranaRep.lean — solution of BookProof.ChapterGhostMajoranaRep.chi2_selfAdjoint
import Mathlib
import Definitions.Def_ChapterGhostMajoranaRep
open BookProof.ChapterGhostMajoranaRep





open Matrix BookProof.GhostField

set_option maxHeartbeats 1000000 in
theorem solution : chi2ᴴ = chi2 := by

  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chi2, psi, psiDag, Matrix.conjTranspose_apply]
