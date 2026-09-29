-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianCanonical.crd_coreState
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:45:08.538388+00:00
-- url     : https://prove2.me/submissions/36ba84fd-949d-4c0b-8cfd-969740ced588

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.crd_coreState
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent














variable (nu : ℝ)
set_option autoImplicit false

theorem solution (β γ : Vel) : crd (coreState β) γ = if γ = β then 1 else 0 := by
  classical
  simp [crd, coreState, lp.single_apply, Pi.single_apply, eq_comm]

#print axioms solution
