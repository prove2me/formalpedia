-- Prove2me | solution 1 for Csg.skirmish_Apre1_home_safe_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:13:06.062799+00:00
-- url     : https://prove2.me/submissions/0eb4d9a3-5b3a-497f-a15e-d747bb8cf096

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_wet_not_mem_Apre1
import Theorems.Thm_Csg_skirmish_hide_not_mem_Apre1_home_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.Apre1 ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ⊆ ({SkirmishPos.home} : Set SkirmishPos) := by
  intro s hs
  cases s with
  | home => rfl
  | hide => exact absurd hs skirmish_hide_not_mem_Apre1_home_safe
  | wet => exact absurd hs (skirmish_wet_not_mem_Apre1 _ skirmishSafe (by decide))
end Csg
