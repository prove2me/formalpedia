-- Prove2me | solution 1 for Csg.skirmishSafe_pre1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:08:52.58047+00:00
-- url     : https://prove2.me/submissions/da397b40-316b-4e29-8730-35ede538da21

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishK_support_hide_hide_throw
import Theorems.Thm_Csg_skirmishK_support_hide_hide_wait
import Theorems.Thm_Csg_skirmishK_support_home


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : skirmishSafe ⊆ skirmishCSG.Pre1 skirmishSafe := by
  intro s hs
  cases s with
  | wet => exact absurd rfl hs
  | hide =>
      refine ⟨.hide, ?_⟩
      intro a2
      cases a2 with
      | wait =>
          rw [skirmishK_support_hide_hide_wait]
          exact Set.singleton_subset_iff.mpr (by decide)
      | throw =>
          rw [skirmishK_support_hide_hide_throw]
          exact Set.singleton_subset_iff.mpr (by decide)
  | home =>
      refine ⟨.hide, ?_⟩
      intro a2
      rw [skirmishK_support_home]
      exact Set.singleton_subset_iff.mpr (by decide)
end Csg
