-- Prove2me | solution 1 for Csg.skirmish_AFVStep_safe_hide_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:15:16.425254+00:00
-- url     : https://prove2.me/submissions/d1aae3b8-f545-4b45-ad17-202de4cdf4c5

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_A_safe_hide_eq_singleton_hide
import Theorems.Thm_Csg_skirmish_B_singleton_hide_safe_hide_eq_univ
import Theorems.Thm_Csg_CSG_A_univ_v2


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.AFVStep skirmishSafe skirmishSafe skirmishSafe SkirmishPos.hide
        ({SoldierMove.hide} : Set SoldierMove)
      = ({SoldierMove.hide} : Set SoldierMove) := by
  change skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide ∩
      skirmishCSG.A
        (skirmishCSG.B ({SoldierMove.hide} : Set SoldierMove) skirmishSafe SkirmishPos.hide)
        skirmishSafe SkirmishPos.hide
    = ({SoldierMove.hide} : Set SoldierMove)
  rw [skirmish_B_singleton_hide_safe_hide_eq_univ, skirmishCSG.A_univ_v2,
    skirmish_A_safe_hide_eq_singleton_hide, Set.inter_univ]
end Csg
