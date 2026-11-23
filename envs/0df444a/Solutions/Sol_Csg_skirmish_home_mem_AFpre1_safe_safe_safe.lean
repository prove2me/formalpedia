-- Prove2me | solution 1 for Csg.skirmish_home_mem_AFpre1_safe_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:15:37.003159+00:00
-- url     : https://prove2.me/submissions/bfde6a85-f39c-477b-bfef-6d885198bdbf

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_hide_mem_AFV_safe_safe_safe_home

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.home ∈ skirmishCSG.AFpre1 skirmishSafe skirmishSafe skirmishSafe :=
  ⟨SoldierMove.hide, skirmish_hide_mem_AFV_safe_safe_safe_home⟩
end Csg
