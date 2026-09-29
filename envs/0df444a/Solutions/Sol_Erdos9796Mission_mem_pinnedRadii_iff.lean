-- Prove2me | solution 1 for Erdos9796Mission.mem_pinnedRadii_iff
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-11T16:41:35.082706+00:00
-- url     : https://prove2.me/submissions/5eb0cd4b-661b-44c7-9370-12c7ba0b75a1

import Definitions.Def_Erdos9796Mission_PinnedMultiplicity

open Erdos9796Mission

theorem solution
    {A : Finset Plane} {p : Plane} {r : ℝ} :
    r ∈ pinnedRadii A p ↔ (∃ q ∈ A, dist p q = r) ∧ 0 < r := by
  simp [pinnedRadii, Finset.mem_filter, Finset.mem_image]
