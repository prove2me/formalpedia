-- Prove2me | solution 1 for BookProof.QuadraticRotation.pgFun_rotPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:13:43.347199+00:00
-- url     : https://prove2.me/submissions/6fd41564-1826-4b3c-a1c7-c2a45198ff16

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.pgFun_rotPoly
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_eval_rotPoly
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
    (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (rotPoly O p) x = pgFun p (rotIso hO x) := by

  rw [pgFun, pgFun, eval_rotPoly hO]
  congr 2
  rw [gaussD, gaussD, (rotIso hO).norm_map x]
