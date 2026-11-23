-- Prove2me | solution 1 for Csg.skirmish_throw_mem_B_singleton_hide_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:10:58.539541+00:00
-- url     : https://prove2.me/submissions/34e991f2-9ec5-42c4-b2df-75f01c3bd055

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishK_support_hide_hide_throw


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SniperMove.throw ∈ skirmishCSG.B ({SoldierMove.hide} : Set SoldierMove)
      ({SkirmishPos.home} : Set SkirmishPos) SkirmishPos.hide := by
  refine ⟨SoldierMove.hide, rfl, SkirmishPos.home, ?_, rfl⟩
  rw [skirmishK_support_hide_hide_throw]
  rfl
end Csg
