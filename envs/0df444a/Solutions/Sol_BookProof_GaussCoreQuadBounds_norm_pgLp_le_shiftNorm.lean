-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.norm_pgLp_le_shiftNorm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:30.507623+00:00
-- url     : https://prove2.me/submissions/9af73aaf-a4e6-468b-9e25-be366e82c827

-- Generated from ChapterGaussCoreQuadBounds.lean — solution of BookProof.GaussCoreQuadBounds.norm_pgLp_le_shiftNorm
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
import Theorems.Thm_BookProof_GaussCoreQuadBounds_quadForm_harm_nonneg
import Theorems.Thm_BookProof_GaussCoreQuadBounds_shiftNorm_sq
import Theorems.Thm_BookProof_GaussCoreQuadBounds_shiftNorm_nonneg
open BookProof.GaussCoreQuadBounds









open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p : MvPolynomial (Fin D) ℂ) : ‖pgLp p‖ ≤ shiftNorm p := by

  have hsq := shiftNorm_sq p
  have hq := quadForm_harm_nonneg p
  nlinarith [norm_nonneg (pgLp p), shiftNorm_nonneg p, sq_nonneg (‖pgLp (harmP p)‖),
    norm_nonneg (pgLp (harmP p))]
