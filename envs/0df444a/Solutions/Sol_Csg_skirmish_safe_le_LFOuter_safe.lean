-- Prove2me | solution 1 for Csg.skirmish_safe_le_LFOuter_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:16:33.448022+00:00
-- url     : https://prove2.me/submissions/bcbb753f-1f85-454e-9c2c-130e53c31d13

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_OrderHom_map_map_bot_le_lfp
import Theorems.Thm_Csg_skirmish_hide_mem_Lpre1_home_safe
import Theorems.Thm_Csg_CSG_Lpre1_empty_x


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishSafe ≤ skirmishCSG.LFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe := by
  have hbot : skirmishCSG.LFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe ⊥
      = ({SkirmishPos.home} : Set SkirmishPos) := by
    change skirmishCSG.Lpre1 (⊥ : Set SkirmishPos) skirmishSafe
        ∪ ({SkirmishPos.home} : Set SkirmishPos) = ({SkirmishPos.home} : Set SkirmishPos)
    rw [Set.bot_eq_empty, skirmishCSG.Lpre1_empty_x, Set.empty_union]
  have hffbot : skirmishSafe ⊆
      skirmishCSG.LFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        (skirmishCSG.LFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe ⊥) := by
    rw [hbot]
    change skirmishSafe ⊆
        skirmishCSG.Lpre1 ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
          ∪ ({SkirmishPos.home} : Set SkirmishPos)
    intro s hs
    cases s with
    | hide => exact Or.inl skirmish_hide_mem_Lpre1_home_safe
    | home => exact Or.inr rfl
    | wet => exact absurd hs (by decide)
  exact hffbot.trans (OrderHom.map_map_bot_le_lfp
    (skirmishCSG.LFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe))
end Csg
