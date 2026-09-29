-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.intertwined_ann
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:40:33.199007+00:00
-- url     : https://prove2.me/submissions/4246bd2e-8be4-4234-8d57-3b60320db2bb

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.intertwined_ann
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_intertwine_ann
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
theorem solution (i : Fin 3) : Intertwined (ann i) (annOp i) :=
  fun x =>
    congrFun (congrArg (fun F : lpFiniteModes Vel →ₗ[ℂ] (polyGaussCore (d := 3)) => ⇑F)
      (intertwine_ann i)) x
