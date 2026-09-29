-- Prove2me | solution 1 for BookProof.HermiteRelative.coreOp_apply_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:59:19.353293+00:00
-- url     : https://prove2.me/submissions/15840cda-66ff-4f8b-b6fc-bc378e6afe79

-- Generated from ChapterHermiteRelativeBound.lean — solution of BookProof.HermiteRelative.coreOp_apply'
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
open BookProof.HermiteRelative










open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}





variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (x : polyGaussCore (d := d)) : coreOp T x = coreEquiv (T (coreEquiv.symm x)) := rfl
