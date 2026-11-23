-- Prove2me | solution 1 for Csg.skirmish_safe_le_LFGX_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:27:29.417797+00:00
-- url     : https://prove2.me/submissions/b5572a8e-1b6f-4dd4-9059-559ef762adb5

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_OrderHom_map_map_bot_le_lfp
import Theorems.Thm_Csg_skirmish_safe_le_LFGY_safe_safe_empty
import Theorems.Thm_Csg_skirmish_safe_le_LFGY_safe_safe_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishSafe ≤ skirmishCSG.LFGX skirmishSafe skirmishSafe := by
  have hmono : skirmishCSG.LFGY skirmishSafe skirmishSafe skirmishSafe ≤
      skirmishCSG.LFGY skirmishSafe skirmishSafe
        (skirmishCSG.LFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos)) :=
    skirmishCSG.LFGY_mono_x skirmishSafe skirmishSafe skirmish_safe_le_LFGY_safe_safe_empty
  have hchain : skirmishSafe ≤
      skirmishCSG.LFGY skirmishSafe skirmishSafe
        (skirmishCSG.LFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos)) :=
    skirmish_safe_le_LFGY_safe_safe_safe.trans hmono
  have hbot : skirmishCSG.LFGMiddle skirmishSafe skirmishSafe (⊥ : Set SkirmishPos)
      = skirmishCSG.LFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos) := by
    change skirmishCSG.LFGY skirmishSafe skirmishSafe (⊥ : Set SkirmishPos)
      = skirmishCSG.LFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos)
    rw [Set.bot_eq_empty]
  have hffbot : skirmishSafe ≤
      skirmishCSG.LFGMiddle skirmishSafe skirmishSafe
        (skirmishCSG.LFGMiddle skirmishSafe skirmishSafe ⊥) := by
    change skirmishSafe ≤ skirmishCSG.LFGY skirmishSafe skirmishSafe
        (skirmishCSG.LFGMiddle skirmishSafe skirmishSafe ⊥)
    rw [hbot]
    exact hchain
  exact hffbot.trans (OrderHom.map_map_bot_le_lfp
    (skirmishCSG.LFGMiddle skirmishSafe skirmishSafe))
end Csg
