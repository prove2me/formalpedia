-- Prove2me | solution 1 for Csg.skirmish_home_le_LGFInnerFun_safe_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:19:57.691471+00:00
-- url     : https://prove2.me/submissions/bdcfe07e-224c-4941-a807-071efbf18cfd

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishSafe_pre1

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    ({SkirmishPos.home} : Set SkirmishPos) ⊆
      skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        (⊥ : Set SkirmishPos) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs
  rw [hs]
  change SkirmishPos.home ∈ (skirmishCSG.Lpre1 (⊥ : Set SkirmishPos) skirmishSafe ∩
      ({SkirmishPos.home} : Set SkirmishPos)ᶜ) ∪
    (skirmishCSG.Pre1 skirmishSafe ∩ ({SkirmishPos.home} : Set SkirmishPos))
  exact Or.inr ⟨skirmishSafe_pre1 (by decide), rfl⟩
end Csg
