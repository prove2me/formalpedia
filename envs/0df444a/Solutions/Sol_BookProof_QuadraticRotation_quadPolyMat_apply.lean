-- Prove2me | solution 1 for BookProof.QuadraticRotation.quadPolyMat_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T19:45:36.331103+00:00
-- url     : https://prove2.me/submissions/c03164c7-22e4-4337-95d5-d20726533203

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.quadPolyMat_apply
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
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
theorem solution (A : Matrix (Fin d) (Fin d) ℝ) (p : MvPolynomial (Fin d) ℂ) :
    quadPolyMat A p = ∑ k, ∑ l, ((A k l : ℝ) : ℂ) •
      (momPoly k (momPoly l p) + (1/4 : ℂ) • (X k * (X l * p))) := by
  -- `mulXPoly_apply` was dropped from the published DifferentialL2 bundle, so
  -- simp cannot unfold `mulXPoly i q` to `X i * q`; state the defeq locally.
  have hmul : ∀ (i : Fin d) (q : MvPolynomial (Fin d) ℂ), mulXPoly i q = X i * q := fun _ _ => rfl
  simp [quadPolyMat, LinearMap.sum_apply, hmul]
