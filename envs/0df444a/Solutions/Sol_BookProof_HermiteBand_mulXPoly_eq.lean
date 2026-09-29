-- Prove2me | solution 1 for BookProof.HermiteBand.mulXPoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:07:23.995266+00:00
-- url     : https://prove2.me/submissions/30fce56c-a3e1-4a21-abb3-e1f3dfcc8342

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.mulXPoly_eq
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) :
    (mulXPoly i : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
      = crePoly i + annPoly i := by

  refine LinearMap.ext fun p => ?_
  simp [mulXPoly, crePoly, annPoly]
