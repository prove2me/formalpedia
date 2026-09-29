-- Prove2me | solution 1 for Erdos9796Mission.not_hasNEquidistantProperty_four_iff_exists_pinnedMultiplicity_le_three
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-11T16:48:47.165926+00:00
-- url     : https://prove2.me/submissions/b2a574dc-ad46-41fc-b1ef-c6e98e98c864

import Definitions.Def_Erdos9796Mission_PinnedMultiplicity
import Theorems.Thm_Erdos9796Mission_hasNEquidistantProperty_iff_forall_le_pinnedMultiplicity

open Erdos9796Mission

theorem solution (A : Finset Plane) :
    ¬ HasNEquidistantProperty 4 A ↔ ∃ p ∈ A, pinnedMultiplicity A p ≤ 3 := by
  rw [Erdos9796Mission.hasNEquidistantProperty_iff_forall_le_pinnedMultiplicity
    (by norm_num : 0 < 4)]
  push Not
  constructor
  · rintro ⟨p, hp, hlt⟩
    exact ⟨p, hp, by omega⟩
  · rintro ⟨p, hp, hle⟩
    exact ⟨p, hp, by omega⟩
