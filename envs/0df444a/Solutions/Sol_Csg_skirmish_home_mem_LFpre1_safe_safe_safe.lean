-- Prove2me | solution 1 for Csg.skirmish_home_mem_LFpre1_safe_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:18:26.812071+00:00
-- url     : https://prove2.me/submissions/f3b7096d-ee88-479f-8da4-2f6318f7ea79

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_univ_le_LFV_safe_safe_safe_home

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.home ∈ skirmishCSG.LFpre1 skirmishSafe skirmishSafe skirmishSafe := by
  have hne : (Set.univ : Set SoldierMove).Nonempty := ⟨SoldierMove.hide, Set.mem_univ _⟩
  exact hne.mono skirmish_univ_le_LFV_safe_safe_safe_home
end Csg
