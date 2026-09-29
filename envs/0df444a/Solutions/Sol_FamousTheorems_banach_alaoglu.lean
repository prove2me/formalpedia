-- Prove2me | solution 1 for FamousTheorems.banach_alaoglu
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T06:56:21.83278+00:00
-- url     : https://prove2.me/submissions/6efde70b-3600-4613-92b1-0a95117d3bc1

import Mathlib

open Filter Set Topology

theorem solution {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace 𝕜] {s : Set E}
    (s_nhds : s ∈ 𝓝 (0 : E)) : IsCompact (WeakDual.polar 𝕜 s) :=
  WeakDual.isCompact_polar 𝕜 s_nhds
