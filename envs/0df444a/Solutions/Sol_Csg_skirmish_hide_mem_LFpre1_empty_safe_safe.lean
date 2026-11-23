-- Prove2me | solution 1 for Csg.skirmish_hide_mem_LFpre1_empty_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:17:19.010232+00:00
-- url     : https://prove2.me/submissions/b510a18a-4920-41d0-b592-abf2312ca122

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_hide_mem_A_safe_hide
import Theorems.Thm_Csg_skirmish_A_empty_safe_le_LFV_empty_safe_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.hide ∈ skirmishCSG.LFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe := by
  have hne : (skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide).Nonempty :=
    ⟨SoldierMove.hide, skirmish_hide_mem_A_safe_hide⟩
  exact hne.mono (skirmish_A_empty_safe_le_LFV_empty_safe_safe SkirmishPos.hide)
end Csg
