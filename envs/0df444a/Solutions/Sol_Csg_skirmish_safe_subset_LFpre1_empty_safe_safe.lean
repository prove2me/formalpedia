-- Prove2me | solution 1 for Csg.skirmish_safe_subset_LFpre1_empty_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:19:51.816115+00:00
-- url     : https://prove2.me/submissions/93787652-c272-4906-bfb7-3f2a54bcb070

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_hide_mem_LFpre1_empty_safe_safe
import Theorems.Thm_Csg_skirmish_home_mem_LFpre1_empty_safe_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishSafe ⊆ skirmishCSG.LFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe := by
  intro s hs
  cases s with
  | hide => exact skirmish_hide_mem_LFpre1_empty_safe_safe
  | home => exact skirmish_home_mem_LFpre1_empty_safe_safe
  | wet => exact absurd hs (by decide)
end Csg
