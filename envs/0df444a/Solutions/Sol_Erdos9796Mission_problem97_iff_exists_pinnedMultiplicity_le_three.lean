-- Prove2me | solution 1 for Erdos9796Mission.problem97_iff_exists_pinnedMultiplicity_le_three
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-11T16:50:40.229172+00:00
-- url     : https://prove2.me/submissions/03e16b61-7aa0-4561-8fb8-147366704544

import Definitions.Def_Erdos9796Mission_PinnedMultiplicity
import Theorems.Thm_Erdos9796Mission_not_hasNEquidistantProperty_four_iff_exists_pinnedMultiplicity_le_three

open Erdos9796Mission

theorem solution :
    Problem97 ↔
      ∀ A : Finset Plane, A.Nonempty → ConvexIndep (A : Set Plane) →
        ∃ p ∈ A, pinnedMultiplicity A p ≤ 3 := by
  unfold Problem97
  constructor
  · intro h A hne hconv
    exact
      (Erdos9796Mission.not_hasNEquidistantProperty_four_iff_exists_pinnedMultiplicity_le_three A).mp
        (h A hne hconv)
  · intro h A hne hconv
    exact
      (Erdos9796Mission.not_hasNEquidistantProperty_four_iff_exists_pinnedMultiplicity_le_three A).mpr
        (h A hne hconv)
