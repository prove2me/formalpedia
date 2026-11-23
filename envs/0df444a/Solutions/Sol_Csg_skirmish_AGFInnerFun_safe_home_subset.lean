-- Prove2me | solution 1 for Csg.skirmish_AGFInnerFun_safe_home_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:18:36.091112+00:00
-- url     : https://prove2.me/submissions/822a35ee-500a-46db-861c-34f38d643379

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_Apre1_home_safe_subset

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.AGFInnerFun ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        ({SkirmishPos.home} : Set SkirmishPos)
      ⊆ ({SkirmishPos.home} : Set SkirmishPos) := by
  intro s hs
  rcases hs with ⟨h1, h2⟩ | ⟨_, h2⟩
  · exact absurd (skirmish_Apre1_home_safe_subset h1) h2
  · exact h2
end Csg
