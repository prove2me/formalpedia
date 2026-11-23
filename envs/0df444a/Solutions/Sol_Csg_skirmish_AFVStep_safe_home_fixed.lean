-- Prove2me | solution 1 for Csg.skirmish_AFVStep_safe_home_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:12:15.023014+00:00
-- url     : https://prove2.me/submissions/67070835-f0a2-4441-af07-831ea0ae51d1

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_A_safe_home_eq_univ
import Theorems.Thm_Csg_skirmish_B_univ_safe_home_eq_univ
import Theorems.Thm_Csg_CSG_A_univ_v2


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.AFVStep skirmishSafe skirmishSafe skirmishSafe SkirmishPos.home
        (Set.univ : Set SoldierMove)
      = (Set.univ : Set SoldierMove) := by
  change skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.home ∩
      skirmishCSG.A
        (skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.home)
        skirmishSafe SkirmishPos.home
    = (Set.univ : Set SoldierMove)
  rw [skirmish_B_univ_safe_home_eq_univ, skirmishCSG.A_univ_v2,
    skirmish_A_safe_home_eq_univ, Set.inter_univ]
end Csg
