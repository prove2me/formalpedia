-- Prove2me | solution 1 for Csg.skirmish_home_mem_AFpre1_empty_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:15:45.052989+00:00
-- url     : https://prove2.me/submissions/bb484f58-cb2d-4f80-83b0-750fe354937b

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_hide_mem_AFV_empty_safe_safe_home

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.home ∈ skirmishCSG.AFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe :=
  ⟨SoldierMove.hide, skirmish_hide_mem_AFV_empty_safe_safe_home⟩
end Csg
