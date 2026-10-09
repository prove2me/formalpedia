-- Prove2me | solution 1 for BookProof.ChapterGhostMajoranaRep.chi_anticomm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:46:03.790995+00:00
-- url     : https://prove2.me/submissions/afd3e393-a124-43e6-a7e4-278ecad0b8ae

-- Generated from ChapterGhostMajoranaRep.lean — solution of BookProof.ChapterGhostMajoranaRep.chi_anticomm
import Mathlib
import Definitions.Def_ChapterGhostMajoranaRep
open BookProof.ChapterGhostMajoranaRep





open Matrix BookProof.GhostField

set_option maxHeartbeats 1000000 in
theorem solution : chi1 * chi2 + chi2 * chi1 = 0 := by

  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chi1, chi2, psi, psiDag]
