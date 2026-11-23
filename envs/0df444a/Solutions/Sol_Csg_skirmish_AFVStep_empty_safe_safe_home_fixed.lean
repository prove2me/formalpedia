-- Prove2me | solution 1 for Csg.skirmish_AFVStep_empty_safe_safe_home_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:12:48.262476+00:00
-- url     : https://prove2.me/submissions/d4c22f03-0f32-4da3-a370-de05e500dd58

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_A_safe_home_eq_univ
import Theorems.Thm_Csg_CSG_B_empty_x


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.AFVStep (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.home
        (Set.univ : Set SoldierMove)
      = (Set.univ : Set SoldierMove) := by
  change skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.home ∩
      skirmishCSG.A
        (skirmishCSG.B (Set.univ : Set SoldierMove) (∅ : Set SkirmishPos) SkirmishPos.home)
        skirmishSafe SkirmishPos.home
    = (Set.univ : Set SoldierMove)
  rw [skirmishCSG.B_empty_x, skirmish_A_safe_home_eq_univ, Set.inter_self]
end Csg
