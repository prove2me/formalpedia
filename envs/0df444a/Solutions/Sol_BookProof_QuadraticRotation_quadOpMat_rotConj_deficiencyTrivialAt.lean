-- Prove2me | solution 1 for BookProof.QuadraticRotation.quadOpMat_rotConj_deficiencyTrivialAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:12:38.085135+00:00
-- url     : https://prove2.me/submissions/f3ed689e-97c5-430c-9079-b6352ab5d53f

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.quadOpMat_rotConj_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_rotHermiteLp_mem_core
import Theorems.Thm_BookProof_QuadraticRotation_rotHermiteLp_total
import Theorems.Thm_BookProof_QuadraticRotation_quadOpMat_rotHermiteLp
import Theorems.Thm_BookProof_HyperbolicQuadratic_deficiencyTrivialAt_of_diagonal
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
theorem solution {O : Matrix (Fin d) (Fin d) ℝ}
    (hO : Oᵀ * O = 1) (c : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCore (d := d)) (quadOpMat (rotConj O c)) z :=
  deficiencyTrivialAt_of_diagonal (rotHermiteLp O) (quadSymbol c) (rotHermiteLp_total hO)
      (quadOpMat (rotConj O c)) (rotHermiteLp_mem_core O)
      (fun a h => quadOpMat_rotHermiteLp hO c a h) hz
