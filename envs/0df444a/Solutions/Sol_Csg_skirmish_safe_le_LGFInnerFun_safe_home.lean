-- Prove2me | solution 1 for Csg.skirmish_safe_le_LGFInnerFun_safe_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:20:27.680089+00:00
-- url     : https://prove2.me/submissions/6b8a5ba8-3ced-44cf-b680-6f9c413b6b4b

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishSafe_pre1
import Theorems.Thm_Csg_skirmish_hide_mem_Lpre1_home_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishSafe ⊆
      skirmishCSG.LGFInnerFun ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        ({SkirmishPos.home} : Set SkirmishPos) := by
  intro s hs
  cases s with
  | hide => exact Or.inl ⟨skirmish_hide_mem_Lpre1_home_safe, by decide⟩
  | home => exact Or.inr ⟨skirmishSafe_pre1 (by decide), rfl⟩
  | wet => exact absurd hs (by decide)
end Csg
