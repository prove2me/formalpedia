-- Prove2me | solution 1 for Csg.skirmish_hide_mem_AFV_safe_safe_safe_hide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:17:26.668646+00:00
-- url     : https://prove2.me/submissions/59633326-5a3a-40a6-ae0c-dc797937fb1c

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_AFVStep_safe_hide_fixed

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SoldierMove.hide ∈ skirmishCSG.AFV skirmishSafe skirmishSafe skirmishSafe SkirmishPos.hide :=
  (skirmishCSG.AFVStep skirmishSafe skirmishSafe skirmishSafe SkirmishPos.hide).le_gfp
    (le_of_eq skirmish_AFVStep_safe_hide_fixed.symm) rfl
end Csg
