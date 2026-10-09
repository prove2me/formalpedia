-- Prove2me | solution 1 for BookProof.GraphCore.mem_pushDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:50:07.070857+00:00
-- url     : https://prove2.me/submissions/ec502a29-5252-4642-bcc9-37c0bbedd8d7

-- Generated from ChapterGraphCoreTransfer.lean — solution of BookProof.GraphCore.mem_pushDom
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.GraphCore




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

set_option maxHeartbeats 1000000 in
theorem solution (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (x : D) :
    U (x : F) ∈ pushDom U D := ⟨(x : F), x.2, rfl⟩
