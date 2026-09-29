-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.commDom_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:26:25.158335+00:00
-- url     : https://prove2.me/submissions/1004799e-2191-4a51-a1f1-2177d5eff6c4

import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift
noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem solution (A B : D →ₗ[ℂ] D) (v : D) :
    commDom A B v = A (B v) - B (A v) := by
  rfl
