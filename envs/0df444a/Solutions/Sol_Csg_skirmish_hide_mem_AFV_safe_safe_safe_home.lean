-- Prove2me | solution 1 for Csg.skirmish_hide_mem_AFV_safe_safe_safe_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:13:46.652542+00:00
-- url     : https://prove2.me/submissions/1b91607b-2cb3-4cbb-8240-d8dfcdeb28d0

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_AFVStep_safe_home_fixed

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SoldierMove.hide ∈ skirmishCSG.AFV skirmishSafe skirmishSafe skirmishSafe SkirmishPos.home :=
  (skirmishCSG.AFVStep skirmishSafe skirmishSafe skirmishSafe SkirmishPos.home).le_gfp
    (le_of_eq skirmish_AFVStep_safe_home_fixed.symm) (Set.mem_univ _)
end Csg
