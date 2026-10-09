-- Prove2me | solution 1 for BookProof.ChapterGhostMajoranaRep.psiDag_of_chi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:46:30.937002+00:00
-- url     : https://prove2.me/submissions/005b7938-da18-47af-9dbc-ca34e1c09ebc

-- Generated from ChapterGhostMajoranaRep.lean — solution of BookProof.ChapterGhostMajoranaRep.psiDag_of_chi
import Mathlib
import Definitions.Def_ChapterGhostMajoranaRep
open BookProof.ChapterGhostMajoranaRep





open Matrix BookProof.GhostField

set_option maxHeartbeats 1000000 in
theorem solution : psiDag = (2 : ℂ)⁻¹ • (chi1 + Complex.I • chi2) := by

  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chi1, chi2, psi, psiDag, Complex.I_mul_I] ; norm_num
