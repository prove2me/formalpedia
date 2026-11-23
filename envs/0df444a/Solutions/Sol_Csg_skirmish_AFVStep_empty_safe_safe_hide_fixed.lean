-- Prove2me | solution 1 for Csg.skirmish_AFVStep_empty_safe_safe_hide_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:15:19.330933+00:00
-- url     : https://prove2.me/submissions/099c9d83-2ed7-4c38-9e70-36be2703a5e5

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_A_safe_hide_eq_singleton_hide
import Theorems.Thm_Csg_CSG_B_empty_x


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.AFVStep (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.hide
        ({SoldierMove.hide} : Set SoldierMove)
      = ({SoldierMove.hide} : Set SoldierMove) := by
  change skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide ∩
      skirmishCSG.A
        (skirmishCSG.B ({SoldierMove.hide} : Set SoldierMove) (∅ : Set SkirmishPos)
          SkirmishPos.hide)
        skirmishSafe SkirmishPos.hide
    = ({SoldierMove.hide} : Set SoldierMove)
  rw [skirmishCSG.B_empty_x, skirmish_A_safe_hide_eq_singleton_hide, Set.inter_self]
end Csg
