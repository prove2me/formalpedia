-- Prove2me | solution 1 for Csg.skirmish_safe_le_AFGX_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:26:45.455428+00:00
-- url     : https://prove2.me/submissions/0981cf29-6fa5-4d03-a3ce-9a5ebb07b126

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_OrderHom_map_map_bot_le_lfp
import Theorems.Thm_Csg_skirmish_safe_le_AFGY_safe_safe_safe
import Theorems.Thm_Csg_skirmish_safe_le_AFGY_safe_safe_empty

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishSafe ≤ skirmishCSG.AFGX skirmishSafe skirmishSafe := by
  have hmono : skirmishCSG.AFGY skirmishSafe skirmishSafe skirmishSafe ≤
      skirmishCSG.AFGY skirmishSafe skirmishSafe
        (skirmishCSG.AFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos)) :=
    skirmishCSG.AFGY_mono_x skirmishSafe skirmishSafe skirmish_safe_le_AFGY_safe_safe_empty
  have hchain : skirmishSafe ≤
      skirmishCSG.AFGY skirmishSafe skirmishSafe
        (skirmishCSG.AFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos)) :=
    skirmish_safe_le_AFGY_safe_safe_safe.trans hmono
  have hbot : skirmishCSG.AFGMiddle skirmishSafe skirmishSafe (⊥ : Set SkirmishPos)
      = skirmishCSG.AFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos) := by
    change skirmishCSG.AFGY skirmishSafe skirmishSafe (⊥ : Set SkirmishPos)
      = skirmishCSG.AFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos)
    rw [Set.bot_eq_empty]
  have hffbot : skirmishSafe ≤
      skirmishCSG.AFGMiddle skirmishSafe skirmishSafe
        (skirmishCSG.AFGMiddle skirmishSafe skirmishSafe ⊥) := by
    change skirmishSafe ≤ skirmishCSG.AFGY skirmishSafe skirmishSafe
        (skirmishCSG.AFGMiddle skirmishSafe skirmishSafe ⊥)
    rw [hbot]
    exact hchain
  exact hffbot.trans (OrderHom.map_map_bot_le_lfp
    (skirmishCSG.AFGMiddle skirmishSafe skirmishSafe))
end Csg
