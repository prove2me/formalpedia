-- Prove2me | solution 1 for Csg.skirmish_SGFInnerFun_safe_home_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:14:37.267365+00:00
-- url     : https://prove2.me/submissions/3945e663-505b-439f-9b65-a6a3052552b2

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishReachGoal_pre1_empty

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.SGFInnerFun ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        ({SkirmishPos.home} : Set SkirmishPos)
      ⊆ ({SkirmishPos.home} : Set SkirmishPos) := by
  intro s hs
  rcases hs with ⟨h1, _⟩ | ⟨_, h2⟩
  · rw [skirmishReachGoal_pre1_empty] at h1
    simp at h1
  · exact h2
end Csg
