-- Prove2me | solution 1 for Csg.skirmish_univ_subset_A_throw_safe_hide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:11:22.727185+00:00
-- url     : https://prove2.me/submissions/6eab809a-b85b-4088-88e5-31baf3285fc1

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishK_support_hide_hide_wait
import Theorems.Thm_Csg_skirmishK_support_hide_run_wait


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    (Set.univ : Set SoldierMove) ⊆
      skirmishCSG.A ({SniperMove.throw} : Set SniperMove) skirmishSafe SkirmishPos.hide := by
  intro a1 _
  cases a1 with
  | hide =>
      intro a2
      cases a2 with
      | throw => left; rfl
      | wait =>
          right
          rw [skirmishK_support_hide_hide_wait]
          exact Set.singleton_subset_iff.mpr (by decide)
  | run =>
      intro a2
      cases a2 with
      | throw => left; rfl
      | wait =>
          right
          rw [skirmishK_support_hide_run_wait]
          exact Set.singleton_subset_iff.mpr (by decide)
end Csg
