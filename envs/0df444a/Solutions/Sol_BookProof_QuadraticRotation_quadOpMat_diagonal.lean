-- Prove2me | solution 1 for BookProof.QuadraticRotation.quadOpMat_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:08:00.151379+00:00
-- url     : https://prove2.me/submissions/0bcb45de-b80e-47ab-9960-1226e4863cb6

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.quadOpMat_diagonal
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_quadPolyMat_diagonal
open BookProof.QuadraticRotation




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c : Fin d → ℝ) :
    quadOpMat (Matrix.diagonal c) = quadOp c := by

  rw [quadOpMat, quadOp, quadPolyMat_diagonal]
