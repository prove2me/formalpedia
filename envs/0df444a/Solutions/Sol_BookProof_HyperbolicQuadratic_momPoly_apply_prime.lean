-- Prove2me | solution 1 for BookProof.HyperbolicQuadratic.momPoly_apply_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T09:48:10.75587+00:00
-- url     : https://prove2.me/submissions/b19dc2a7-c8b8-4ccb-aa4e-e5126be35dd3

-- Generated from ChapterHyperbolicQuadraticEsa.lean — solution of BookProof.HyperbolicQuadratic.momPoly_apply'
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_momPoly_apply
open BookProof.HyperbolicQuadratic




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}
variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i p = (-Complex.I) • (pderiv i p - (1/2 : ℂ) • (X i * p)) := by

  rw [momPoly_apply, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
