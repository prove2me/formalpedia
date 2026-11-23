-- Prove2me | solution 1 for Csg.skirmish_hide_mem_LFpre1_safe_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:20:11.528901+00:00
-- url     : https://prove2.me/submissions/7dbe1c6c-c5a6-47e0-8d6e-568d41680b9f

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_univ_le_LFV_safe_safe_safe_hide

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.hide ∈ skirmishCSG.LFpre1 skirmishSafe skirmishSafe skirmishSafe := by
  have hne : (Set.univ : Set SoldierMove).Nonempty := ⟨SoldierMove.hide, Set.mem_univ _⟩
  exact hne.mono skirmish_univ_le_LFV_safe_safe_safe_hide
end Csg
