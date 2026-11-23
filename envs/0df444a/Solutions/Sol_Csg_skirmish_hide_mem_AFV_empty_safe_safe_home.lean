-- Prove2me | solution 1 for Csg.skirmish_hide_mem_AFV_empty_safe_safe_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:13:55.545792+00:00
-- url     : https://prove2.me/submissions/52563861-c127-4f95-b321-98c3097dff5b

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_AFVStep_empty_safe_safe_home_fixed

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SoldierMove.hide ∈
      skirmishCSG.AFV (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.home :=
  (skirmishCSG.AFVStep (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.home).le_gfp
    (le_of_eq skirmish_AFVStep_empty_safe_safe_home_fixed.symm) (Set.mem_univ _)
end Csg
