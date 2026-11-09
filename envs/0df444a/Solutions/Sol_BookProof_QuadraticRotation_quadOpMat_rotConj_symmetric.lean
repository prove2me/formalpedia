-- Prove2me | solution 1 for BookProof.QuadraticRotation.quadOpMat_rotConj_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:07:41.242201+00:00
-- url     : https://prove2.me/submissions/0a08a115-a106-49d9-b58c-0d4d74148436

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.quadOpMat_rotConj_symmetric
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_orthonormal_rotHermiteLp
import Theorems.Thm_BookProof_QuadraticRotation_span_rotHermiteLp
import Theorems.Thm_BookProof_QuadraticRotation_quadOpMat_rotHermiteLp
import Theorems.Thm_BookProof_HyperbolicQuadratic_symmetricOn_of_diagonal
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
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) : SymmetricOn (polyGaussCore (d := d)) (quadOpMat (rotConj O c)) :=
  symmetricOn_of_diagonal (rotHermiteLp O) (orthonormal_rotHermiteLp hO) (quadSymbol c)
      (span_rotHermiteLp hO) (quadOpMat (rotConj O c))
      (fun a h => quadOpMat_rotHermiteLp hO c a h)
