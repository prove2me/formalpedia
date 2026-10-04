-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.mulXPoly_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:07:09.819067+00:00
-- url     : https://prove2.me/submissions/53c9c62a-653e-4530-87ef-d48d28c7c97d

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.mulXPoly_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.NavierStokesFlow.DifferentialL2




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulXPoly i p = X i * p := rfl
