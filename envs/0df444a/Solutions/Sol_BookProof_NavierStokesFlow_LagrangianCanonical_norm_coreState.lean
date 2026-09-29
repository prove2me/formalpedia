-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianCanonical.norm_coreState
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:34:08.684595+00:00
-- url     : https://prove2.me/submissions/97bf1f05-ec42-4e3b-aa4d-0c258c1d6007

import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent
theorem solution (β : Vel) : ‖((coreState β : lpFiniteModes Vel) : L2I Vel)‖ = 1 := by
  simp [coreState]
