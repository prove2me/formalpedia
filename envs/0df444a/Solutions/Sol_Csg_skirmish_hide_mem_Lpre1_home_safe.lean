-- Prove2me | solution 1 for Csg.skirmish_hide_mem_Lpre1_home_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:14:22.229966+00:00
-- url     : https://prove2.me/submissions/ba9d4ad4-f6e5-4813-ac26-17a528a02e66

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_LW_home_safe_hide_eq_univ
import Theorems.Thm_Csg_skirmish_B_univ_home_hide_eq_univ

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.hide ∈ skirmishCSG.Lpre1 ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe := by
  change skirmishCSG.B
      (skirmishCSG.LW ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe SkirmishPos.hide)
      ({SkirmishPos.home} : Set SkirmishPos) SkirmishPos.hide = (Set.univ : Set SniperMove)
  rw [skirmish_LW_home_safe_hide_eq_univ]
  exact skirmish_B_univ_home_hide_eq_univ
end Csg
