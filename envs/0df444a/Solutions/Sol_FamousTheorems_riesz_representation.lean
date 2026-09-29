-- Prove2me | solution 1 for FamousTheorems.riesz_representation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:08:22.230791+00:00
-- url     : https://prove2.me/submissions/0638e69c-9e59-4669-8fcb-0ea9175383cc

import Mathlib

theorem solution (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    ∃ Φ : E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E, ∀ x y : E, Φ x y = inner 𝕜 x y :=
  ⟨InnerProductSpace.toDual 𝕜 E, fun _ _ => rfl⟩
