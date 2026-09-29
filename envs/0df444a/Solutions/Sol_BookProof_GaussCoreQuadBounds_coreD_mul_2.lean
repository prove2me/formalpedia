-- Prove2me | solution 2 for BookProof.GaussCoreQuadBounds.coreD_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T13:22:15.927353+00:00
-- url     : https://prove2.me/submissions/e40bda9a-6cad-4d3d-98a1-2659a21c11df

-- Generated from ChapterGaussCoreQuadBounds.lean — solution of BookProof.GaussCoreQuadBounds.coreD_mul
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds









open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin D) (f p : MvPolynomial (Fin D) ℂ) :
    coreD j (f * p) = pderiv j f * p + f * coreD j p := by

  simp only [coreD, pderiv_mul, mul_sub]
  ring
