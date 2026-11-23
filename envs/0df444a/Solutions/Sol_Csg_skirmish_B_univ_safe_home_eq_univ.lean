-- Prove2me | solution 1 for Csg.skirmish_B_univ_safe_home_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:08:49.203006+00:00
-- url     : https://prove2.me/submissions/74a748d4-fba8-4144-b228-cda9547700ba

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishK_support_home


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.home
      = (Set.univ : Set SniperMove) := by
  apply Set.eq_univ_of_forall
  intro a2
  refine ⟨SoldierMove.hide, Set.mem_univ _, SkirmishPos.hide, ?_, by decide⟩
  rw [skirmishK_support_home]
  rfl
end Csg
