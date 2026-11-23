-- Prove2me | solution 1 for Csg.skirmish_hide_mem_AFpre1_safe_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:19:07.872911+00:00
-- url     : https://prove2.me/submissions/c80c9d9c-6a9e-4e68-898f-96b66bb13651

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_hide_mem_AFV_safe_safe_safe_hide

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.hide ∈ skirmishCSG.AFpre1 skirmishSafe skirmishSafe skirmishSafe :=
  ⟨SoldierMove.hide, skirmish_hide_mem_AFV_safe_safe_safe_hide⟩
end Csg
