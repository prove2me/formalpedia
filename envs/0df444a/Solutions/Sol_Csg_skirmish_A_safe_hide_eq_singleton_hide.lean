-- Prove2me | solution 1 for Csg.skirmish_A_safe_hide_eq_singleton_hide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:13:36.094459+00:00
-- url     : https://prove2.me/submissions/2de0a2a4-b2a4-4b29-b0c9-2e28a35c466e

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_hide_mem_A_safe_hide
import Theorems.Thm_Csg_skirmish_run_not_mem_A_safe_hide

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide = {SoldierMove.hide} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨skirmish_hide_mem_A_safe_hide, ?_⟩
  intro a1 ha1
  cases a1 with
  | hide => rfl
  | run => exact absurd ha1 skirmish_run_not_mem_A_safe_hide
end Csg
