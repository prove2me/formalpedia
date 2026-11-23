-- Prove2me | solution 1 for Csg.skirmish_SGFInnerFun_top_safe_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:16:51.132801+00:00
-- url     : https://prove2.me/submissions/5f2a5f48-01bc-4ef5-ba0b-3f986773e9ab

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_wet_not_mem_Pre1

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.SGFInnerFun ({SkirmishPos.home} : Set SkirmishPos) (⊤ : Set SkirmishPos)
        skirmishSafe
      ⊆ skirmishSafe := by
  intro s hs
  rcases hs with ⟨h1, _⟩ | ⟨_, h2⟩
  · cases s with
    | hide => decide
    | home => decide
    | wet => exact absurd h1 (skirmish_wet_not_mem_Pre1 skirmishSafe (by decide))
  · rw [Set.eq_of_mem_singleton h2]
    decide
end Csg
