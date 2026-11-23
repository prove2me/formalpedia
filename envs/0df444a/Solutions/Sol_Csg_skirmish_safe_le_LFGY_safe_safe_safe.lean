-- Prove2me | solution 1 for Csg.skirmish_safe_le_LFGY_safe_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:25:27.266817+00:00
-- url     : https://prove2.me/submissions/83d02327-3670-4188-abf0-af00e5d53e06

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_safe_le_LFGInner_safe_safe_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishSafe ≤ skirmishCSG.LFGY skirmishSafe skirmishSafe skirmishSafe :=
  (skirmishCSG.LFGInner skirmishSafe skirmishSafe skirmishSafe).le_gfp
    skirmish_safe_le_LFGInner_safe_safe_safe
end Csg
