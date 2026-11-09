-- Prove2me | solution 1 for BookProof.QuadraticRotation.quadPolyMat_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:59:05.739127+00:00
-- url     : https://prove2.me/submissions/603a6d48-030e-4941-b7dc-d3b01e3bd122

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.quadPolyMat_diagonal
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_quadPolyMat_apply
import Theorems.Thm_BookProof_QuadraticRotation_quadPoly_apply_prime
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
    quadPolyMat (Matrix.diagonal c) = quadPoly c := by

  refine LinearMap.ext fun p => ?_
  rw [quadPolyMat_apply, quadPoly_apply_prime]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
  simp
