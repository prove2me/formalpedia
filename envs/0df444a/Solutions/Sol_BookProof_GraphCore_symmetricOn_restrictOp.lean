-- Prove2me | solution 1 for BookProof.GraphCore.symmetricOn_restrictOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:48:11.551093+00:00
-- url     : https://prove2.me/submissions/e56b47bc-e71f-4c12-9fc2-4d9c83b356a5

-- Generated from ChapterGraphCoreTransfer.lean — solution of BookProof.GraphCore.symmetricOn_restrictOp
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.GraphCore




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) (h : D₁ ≤ D₂)
    (hT : SymmetricOn D₂ T) : SymmetricOn D₁ (restrictOp T h) := fun x y => hT ⟨(x : F), h x.2⟩ ⟨(y : F), h y.2⟩
