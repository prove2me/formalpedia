-- Prove2me | solution 1 for BookProof.ChapterGhostMajoranaRep.chi2_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:46:02.701248+00:00
-- url     : https://prove2.me/submissions/6918d0d8-5b54-4727-872d-9af4bdbf7700

-- Generated from ChapterGhostMajoranaRep.lean — solution of BookProof.ChapterGhostMajoranaRep.chi2_sq
import Mathlib
import Definitions.Def_ChapterGhostMajoranaRep
open BookProof.ChapterGhostMajoranaRep





open Matrix BookProof.GhostField

set_option maxHeartbeats 1000000 in
theorem solution : chi2 * chi2 = 1 := by

  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chi2, psi, psiDag, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]
