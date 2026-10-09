-- Prove2me | solution 1 for BookProof.ChapterGhostMajoranaRep.psi_of_chi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:46:05.017666+00:00
-- url     : https://prove2.me/submissions/890ddd9e-7432-40df-acb2-765f6711866d

-- Generated from ChapterGhostMajoranaRep.lean — solution of BookProof.ChapterGhostMajoranaRep.psi_of_chi
import Mathlib
import Definitions.Def_ChapterGhostMajoranaRep
open BookProof.ChapterGhostMajoranaRep





open Matrix BookProof.GhostField

set_option maxHeartbeats 1000000 in
theorem solution : psi = (2 : ℂ)⁻¹ • (chi1 - Complex.I • chi2) := by

  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chi1, chi2, psi, psiDag, Complex.I_mul_I] ; norm_num
