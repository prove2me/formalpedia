-- Prove2me | solution 1 for Csg.skirmish_safe_le_LFGY_safe_safe_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:23:13.79666+00:00
-- url     : https://prove2.me/submissions/71cb0aec-58f8-434b-b2dd-7a92ff371d9c

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_safe_le_LFGInner_safe_safe_empty

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishSafe ≤ skirmishCSG.LFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos) :=
  (skirmishCSG.LFGInner skirmishSafe skirmishSafe (∅ : Set SkirmishPos)).le_gfp
    skirmish_safe_le_LFGInner_safe_safe_empty
end Csg
