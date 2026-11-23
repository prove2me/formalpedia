-- Prove2me | solution 1 for Csg.skirmish_B_singleton_hide_safe_hide_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:09:34.717261+00:00
-- url     : https://prove2.me/submissions/c1186b95-57be-4360-8138-aa438140eb28

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishK_support_hide_hide_throw
import Theorems.Thm_Csg_skirmishK_support_hide_hide_wait


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.B ({SoldierMove.hide} : Set SoldierMove) skirmishSafe SkirmishPos.hide
      = (Set.univ : Set SniperMove) := by
  apply Set.eq_univ_of_forall
  intro a2
  cases a2 with
  | wait =>
      refine ⟨SoldierMove.hide, rfl, SkirmishPos.hide, ?_, by decide⟩
      rw [skirmishK_support_hide_hide_wait]
      rfl
  | throw =>
      refine ⟨SoldierMove.hide, rfl, SkirmishPos.home, ?_, by decide⟩
      rw [skirmishK_support_hide_hide_throw]
      rfl
end Csg
