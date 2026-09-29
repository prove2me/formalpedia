-- Prove2me | solution 1 for FamousTheorems.closed_graph_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:51:39.860223+00:00
-- url     : https://prove2.me/submissions/7a1827b5-0042-4d5d-babc-ae094cf6718e

import Mathlib

theorem solution {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) : Continuous g :=
  LinearMap.continuous_of_isClosed_graph g hg
