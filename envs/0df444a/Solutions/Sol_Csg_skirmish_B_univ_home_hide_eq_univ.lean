-- Prove2me | solution 1 for Csg.skirmish_B_univ_home_hide_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:11:27.760146+00:00
-- url     : https://prove2.me/submissions/51ec4876-c770-41b0-bf2e-22ea20b5a480

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishK_support_hide_hide_throw
import Theorems.Thm_Csg_skirmishK_support_hide_run_wait


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.B (Set.univ : Set SoldierMove) ({SkirmishPos.home} : Set SkirmishPos)
      SkirmishPos.hide = (Set.univ : Set SniperMove) := by
  apply Set.eq_univ_of_forall
  intro a2
  cases a2 with
  | wait =>
      refine ⟨SoldierMove.run, Set.mem_univ _, SkirmishPos.home, ?_, rfl⟩
      rw [skirmishK_support_hide_run_wait]
      rfl
  | throw =>
      refine ⟨SoldierMove.hide, Set.mem_univ _, SkirmishPos.home, ?_, rfl⟩
      rw [skirmishK_support_hide_hide_throw]
      rfl
end Csg
