-- Prove2me | solution 1 for BookProof.GraphCore.pushDom_mono
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T14:06:51.740733+00:00
-- url     : https://prove2.me/submissions/a736892c-e86b-4c3a-9632-8fc28bc7829b

-- Generated from ChapterGraphCoreTransfer.lean — solution of BookProof.GraphCore.pushDom_mono
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.GraphCore




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

set_option maxHeartbeats 1000000 in
theorem solution (U : F →ₗᵢ[ℂ] G) {D₁ D₂ : Submodule ℂ F} (h : D₁ ≤ D₂) :
    pushDom U D₁ ≤ pushDom U D₂ := Submodule.map_mono h
