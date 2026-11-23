-- Prove2me | solution 1 for Csg.skirmish_univ_le_LFV_safe_safe_safe_hide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:17:58.996895+00:00
-- url     : https://prove2.me/submissions/82444d67-d51d-40e5-a7c1-8b88a785ef1a

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_LFW_univ_safe_hide_eq_univ

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    (Set.univ : Set SoldierMove) ≤
      skirmishCSG.LFV skirmishSafe skirmishSafe skirmishSafe SkirmishPos.hide :=
  (skirmishCSG.LFVStep skirmishSafe skirmishSafe skirmishSafe SkirmishPos.hide).le_gfp
    (le_of_eq skirmish_LFW_univ_safe_hide_eq_univ.symm)
end Csg
