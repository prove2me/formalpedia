-- Prove2me | solution 1 for BookProof.HermiteRelative.coreOp_comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:45:25.967974+00:00
-- url     : https://prove2.me/submissions/63a5e3c5-647e-4430-b181-22596bfd6284

-- Generated from ChapterHermiteRelativeBound.lean — solution of BookProof.HermiteRelative.coreOp_comp
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Theorems.Thm_BookProof_HermiteRelative_coreOp_apply_prime
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
theorem solution (S T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) :
    coreOp (S.comp T) = (coreOp S).comp (coreOp T) := by

  refine LinearMap.ext fun x => ?_
  simp [coreOp_apply_prime]
