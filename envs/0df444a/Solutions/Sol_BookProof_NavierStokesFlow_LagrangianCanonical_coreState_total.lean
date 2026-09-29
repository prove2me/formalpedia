-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianCanonical.coreState_total
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:45:09.407568+00:00
-- url     : https://prove2.me/submissions/92d6d5bf-bcdb-4c4f-831f-2ddca4f19531

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.coreState_total
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent














variable (nu : ℝ)
set_option autoImplicit false

theorem solution (w : L2I Vel)
    (hw : ∀ β : Vel, (inner ℂ ((coreState β : lpFiniteModes Vel) : L2I Vel) w : ℂ) = 0) :
    w = 0 := by
  apply lp.ext
  funext β
  have h := hw β
  simpa [coreState, lp.inner_single_left] using h

#print axioms solution
