-- Prove2me | solution 1 for BookProof.QuadraticRotation.rotPoly_X
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:00:17.446233+00:00
-- url     : https://prove2.me/submissions/f8f72496-53db-450d-9b8f-1d51bfae49e2

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.rotPoly_X
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
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
theorem solution (O : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    rotPoly O (X i) = ∑ j, C ((O j i : ℝ) : ℂ) * X j := by

  simp [rotPoly]
