-- Prove2me | solution 1 for Csg.skirmish_AGFOuter_safe_le_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:20:49.065309+00:00
-- url     : https://prove2.me/submissions/9728db68-9281-4452-b40e-7f1aacf0024f

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_AGFInnerFun_safe_home_subset

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.AGFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ≤ ({SkirmishPos.home} : Set SkirmishPos) :=
  (skirmishCSG.AGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe).lfp_le
    skirmish_AGFInnerFun_safe_home_subset
end Csg
