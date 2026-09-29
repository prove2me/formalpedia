-- Prove2me | solution 1 for FamousTheorems.hellinger_toeplitz
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:10:16.009989+00:00
-- url     : https://prove2.me/submissions/749c4a1e-0c70-49f2-bd8a-4af762feeca6

import Mathlib

theorem solution {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) : Continuous T :=
  hT.continuous
