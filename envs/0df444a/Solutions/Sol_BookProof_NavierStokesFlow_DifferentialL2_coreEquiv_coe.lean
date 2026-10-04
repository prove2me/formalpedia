-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.coreEquiv_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-02T17:07:11.146551+00:00
-- url     : https://prove2.me/submissions/7699a15c-e91b-4520-a9a4-514927e60aa8

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.coreEquiv_coe
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
theorem solution (p : MvPolynomial (Fin d) ℂ) :
    ((coreEquiv p : polyGaussCore (d := d)) : L2d d) = pgLp p := rfl
