-- Prove2me | solution 1 for Csg.skirmish_AFOuter_top_le_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:12:09.931101+00:00
-- url     : https://prove2.me/submissions/270e8e53-4f23-4848-ad78-1f0628aa123e

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_Apre1_safe_top_subset

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.AFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤ ≤ skirmishSafe := by
  apply (skirmishCSG.AFInner ({SkirmishPos.home} : Set SkirmishPos) ⊤).lfp_le
  change skirmishCSG.Apre1 skirmishSafe (⊤ : Set SkirmishPos)
      ∪ ({SkirmishPos.home} : Set SkirmishPos) ⊆ skirmishSafe
  exact Set.union_subset skirmish_Apre1_safe_top_subset
    (Set.singleton_subset_iff.mpr (by decide))
end Csg
