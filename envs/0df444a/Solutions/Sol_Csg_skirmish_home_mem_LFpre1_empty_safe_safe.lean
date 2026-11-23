-- Prove2me | solution 1 for Csg.skirmish_home_mem_LFpre1_empty_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:17:49.448556+00:00
-- url     : https://prove2.me/submissions/73dc0c4f-c2a0-4d84-ab80-7250dfc432f4

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_A_safe_home_eq_univ
import Theorems.Thm_Csg_skirmish_A_empty_safe_le_LFV_empty_safe_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.home ∈ skirmishCSG.LFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe := by
  have hne : (skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.home).Nonempty := by
    rw [skirmish_A_safe_home_eq_univ]
    exact ⟨SoldierMove.hide, Set.mem_univ _⟩
  exact hne.mono (skirmish_A_empty_safe_le_LFV_empty_safe_safe SkirmishPos.home)
end Csg
