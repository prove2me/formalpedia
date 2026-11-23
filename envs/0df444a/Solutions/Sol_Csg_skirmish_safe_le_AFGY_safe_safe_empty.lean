-- Prove2me | solution 1 for Csg.skirmish_safe_le_AFGY_safe_safe_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:24:45.075411+00:00
-- url     : https://prove2.me/submissions/32d38e56-6998-4ba1-946a-4b1b84971801

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_safe_le_AFGInner_safe_safe_empty

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishSafe ≤ skirmishCSG.AFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos) :=
  (skirmishCSG.AFGInner skirmishSafe skirmishSafe (∅ : Set SkirmishPos)).le_gfp
    skirmish_safe_le_AFGInner_safe_safe_empty
end Csg
