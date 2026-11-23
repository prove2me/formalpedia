-- Prove2me | solution 1 for Csg.skirmish_univ_le_LFV_safe_safe_safe_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:16:47.068559+00:00
-- url     : https://prove2.me/submissions/0cd897a8-6b00-4ae2-815f-33f980848350

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_LFW_univ_safe_home_eq_univ

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    (Set.univ : Set SoldierMove) ≤
      skirmishCSG.LFV skirmishSafe skirmishSafe skirmishSafe SkirmishPos.home :=
  (skirmishCSG.LFVStep skirmishSafe skirmishSafe skirmishSafe SkirmishPos.home).le_gfp
    (le_of_eq skirmish_LFW_univ_safe_home_eq_univ.symm)
end Csg
