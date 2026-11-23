-- Prove2me | solution 1 for Csg.skirmish_SGFOuter_safe_le_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:17:54.806847+00:00
-- url     : https://prove2.me/submissions/2f5b8a6c-73e6-4799-8523-574af92dcee7

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_SGFInnerFun_safe_home_subset

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.SGFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ≤ ({SkirmishPos.home} : Set SkirmishPos) :=
  (skirmishCSG.SGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe).lfp_le
    skirmish_SGFInnerFun_safe_home_subset
end Csg
