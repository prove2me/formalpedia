-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.momPoly_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:05:22.851367+00:00
-- url     : https://prove2.me/submissions/aeb2f5cc-6cf1-4625-8f87-ddb2b4c7e622

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.momPoly_apply
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
    momPoly i p = C (-Complex.I) * (pderiv i p - C (1/2 : ℂ) * (X i * p)) := rfl
