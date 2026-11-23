-- Prove2me | solution 1 for Csg.skirmish_hide_mem_A_safe_hide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:09:04.98521+00:00
-- url     : https://prove2.me/submissions/9aee4fbb-c571-4158-b368-cddd4c061677

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishK_support_hide_hide_throw
import Theorems.Thm_Csg_skirmishK_support_hide_hide_wait


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SoldierMove.hide ∈ skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide := by
  intro a2
  cases a2 with
  | wait =>
      right
      rw [skirmishK_support_hide_hide_wait]
      exact Set.singleton_subset_iff.mpr (by decide)
  | throw =>
      right
      rw [skirmishK_support_hide_hide_throw]
      exact Set.singleton_subset_iff.mpr (by decide)
end Csg
