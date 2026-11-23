-- Prove2me | solution 1 for Csg.skirmish_hide_mem_AFV_empty_safe_safe_hide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:17:29.640181+00:00
-- url     : https://prove2.me/submissions/5e896891-58ef-4ab0-b283-ed7e9bc3c9d9

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_AFVStep_empty_safe_safe_hide_fixed

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SoldierMove.hide ∈
      skirmishCSG.AFV (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.hide :=
  (skirmishCSG.AFVStep (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.hide).le_gfp
    (le_of_eq skirmish_AFVStep_empty_safe_safe_hide_fixed.symm) rfl
end Csg
