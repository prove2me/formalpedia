-- Prove2me | solution 1 for Csg.skirmish_safe_le_AFGY_safe_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:24:27.815412+00:00
-- url     : https://prove2.me/submissions/c8175143-2718-413e-84ae-3f3fc42ce0da

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_safe_le_AFGInner_safe_safe_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishSafe ≤ skirmishCSG.AFGY skirmishSafe skirmishSafe skirmishSafe :=
  (skirmishCSG.AFGInner skirmishSafe skirmishSafe skirmishSafe).le_gfp
    skirmish_safe_le_AFGInner_safe_safe_safe
end Csg
