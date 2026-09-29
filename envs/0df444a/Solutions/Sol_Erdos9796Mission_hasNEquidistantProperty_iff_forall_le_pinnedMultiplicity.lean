-- Prove2me | solution 1 for Erdos9796Mission.hasNEquidistantProperty_iff_forall_le_pinnedMultiplicity
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-11T16:47:06.813987+00:00
-- url     : https://prove2.me/submissions/f4cadbfd-c763-4193-b1e9-235a6378914a

import Definitions.Def_Erdos9796Mission_PinnedMultiplicity
import Theorems.Thm_Erdos9796Mission_hasNEquidistantPointsAt_iff_le_pinnedMultiplicity

open Erdos9796Mission

theorem solution
    {A : Finset Plane} {n : ℕ} (hn : 0 < n) :
    HasNEquidistantProperty n A ↔ ∀ p ∈ A, n ≤ pinnedMultiplicity A p := by
  constructor
  · intro h p hp
    exact (Erdos9796Mission.hasNEquidistantPointsAt_iff_le_pinnedMultiplicity hn).mp
      (h p hp)
  · intro h p hp
    exact (Erdos9796Mission.hasNEquidistantPointsAt_iff_le_pinnedMultiplicity hn).mpr
      (h p hp)
