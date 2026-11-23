-- Prove2me | solution 1 for Csg.skirmish_run_not_mem_A_safe_hide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:12:07.121905+00:00
-- url     : https://prove2.me/submissions/c51ff8fc-3e08-4f6d-99f4-41fd1d7c4574

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishK_support_hide_run_throw


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SoldierMove.run ∉ skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide := by
  intro hrun
  rcases hrun SniperMove.throw with h | h
  · exact h
  · rw [skirmishK_support_hide_run_throw] at h
    exact absurd (Set.singleton_subset_iff.mp h) (by decide)
end Csg
