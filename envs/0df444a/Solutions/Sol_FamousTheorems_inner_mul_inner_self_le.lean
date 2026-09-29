-- Prove2me | solution 1 for FamousTheorems.inner_mul_inner_self_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:17:24.770483+00:00
-- url     : https://prove2.me/submissions/b9dd0edf-66a5-4f94-ad92-92372e326bc8

import Mathlib

theorem solution : ∀ {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (x y : E),
    ‖(inner 𝕜 x y : 𝕜)‖ * ‖(inner 𝕜 y x : 𝕜)‖ ≤
      RCLike.re (inner 𝕜 x x : 𝕜) * RCLike.re (inner 𝕜 y y : 𝕜) :=
  inner_mul_inner_self_le
