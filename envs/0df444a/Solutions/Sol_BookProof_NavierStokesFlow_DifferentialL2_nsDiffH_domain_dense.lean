-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.nsDiffH_domain_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:19:05.26977+00:00
-- url     : https://prove2.me/submissions/48696a11-a2f1-48a1-a93d-c7d7609b8b21

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.nsDiffH_domain_dense
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

set_option maxHeartbeats 1000000 in
theorem solution :
    Dense ((polyGaussCore (d := 3) : Submodule ℂ (L2d 3)) : Set (L2d 3)) := polyGaussCore_dense
