-- Prove2me | solution 1 for FamousTheorems.von_neumann_mean_ergodic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:23:34.352986+00:00
-- url     : https://prove2.me/submissions/af3ae366-60ea-41c0-8372-2fcaecff2058

import Mathlib

theorem solution {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (f : E →L[𝕜] E) (hf : ‖f‖ ≤ 1) (x : E) :
    Filter.Tendsto (fun n => birkhoffAverage 𝕜 f id n x) Filter.atTop
      (nhds (((f.eqLocus (1 : E →L[𝕜] E)).orthogonalProjectionOnto x : E))) :=
  ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection f hf x
