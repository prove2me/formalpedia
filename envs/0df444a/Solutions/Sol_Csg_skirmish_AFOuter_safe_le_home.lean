-- Prove2me | solution 1 for Csg.skirmish_AFOuter_safe_le_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:14:25.355054+00:00
-- url     : https://prove2.me/submissions/7993f017-1d1c-440e-8a38-fe3716be55ed

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
    skirmishCSG.AFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ≤ ({SkirmishPos.home} : Set SkirmishPos) := by
  apply (skirmishCSG.AFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe).lfp_le
  change skirmishCSG.Apre1 ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ∪ ({SkirmishPos.home} : Set SkirmishPos) ⊆ ({SkirmishPos.home} : Set SkirmishPos)
  exact Set.union_subset skirmish_Apre1_home_safe_subset (Set.Subset.refl _)
end Csg
