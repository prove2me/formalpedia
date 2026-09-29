-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.coe_sum_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:32:12.563038+00:00
-- url     : https://prove2.me/submissions/5bf56585-f1ea-4746-b6a5-559951461ed9

import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F} {κ : Type*}

theorem solution (s : Finset κ) (A : κ → (D →ₗ[ℂ] D)) (v : D) :
    (((∑ k ∈ s, A k) v : D) : F) = ∑ k ∈ s, ((A k v : D) : F) := by
  simp
