-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.norm_kinPoly_le_shiftNorm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:38:22.456472+00:00
-- url     : https://prove2.me/submissions/4c49213b-cf0d-4839-bbdf-5b9b10e7a585

-- Generated from ChapterGaussCoreQuadBounds.lean — solution of BookProof.GaussCoreQuadBounds.norm_kinPoly_le_shiftNorm
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
import Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_harmP_le_shiftNorm
import Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_harmPoly_mul_le_shiftNorm
open BookProof.GaussCoreQuadBounds









open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (kinPoly p)‖ ≤ 3 * shiftNorm p := by

  have hadd : pgLp (kinPoly p + harmPoly * p) = pgLp (kinPoly p) + pgLp (harmPoly * p) := by
    rw [← pgMap_apply, ← pgMap_apply, ← pgMap_apply, map_add]
  have heq : pgLp (kinPoly p) = pgLp (harmP p) - pgLp (harmPoly * p) := by
    rw [harmP, hadd]
    abel
  have h1 : ‖pgLp (harmP p)‖ ≤ shiftNorm p := norm_harmP_le_shiftNorm p
  have h2 : ‖pgLp (harmPoly * p)‖ ≤ 2 * shiftNorm p := norm_harmPoly_mul_le_shiftNorm p
  calc ‖pgLp (kinPoly p)‖ = ‖pgLp (harmP p) - pgLp (harmPoly * p)‖ := by rw [heq]
    _ ≤ ‖pgLp (harmP p)‖ + ‖pgLp (harmPoly * p)‖ := norm_sub_le _ _
    _ ≤ 3 * shiftNorm p := by linarith
