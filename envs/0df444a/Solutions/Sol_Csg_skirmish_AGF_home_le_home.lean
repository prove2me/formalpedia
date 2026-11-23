-- Prove2me | solution 1 for Csg.skirmish_AGF_home_le_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:22:58.346966+00:00
-- url     : https://prove2.me/submissions/2fa9279a-32c3-4dda-aed6-7e0bea2dcf5b

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_OrderHom_gfp_le_map_map_top
import Theorems.Thm_Csg_skirmish_AGFOuter_top_le_safe
import Theorems.Thm_Csg_skirmish_AGFOuter_safe_le_home

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.AGF ({SkirmishPos.home} : Set SkirmishPos)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) := by
  have hstep : skirmishCSG.AGFOuter ({SkirmishPos.home} : Set SkirmishPos)
      (skirmishCSG.AGFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) :=
    ((skirmishCSG.AGFOuter ({SkirmishPos.home} : Set SkirmishPos)).mono
      skirmish_AGFOuter_top_le_safe).trans skirmish_AGFOuter_safe_le_home
  exact (OrderHom.gfp_le_map_map_top
      (skirmishCSG.AGFOuter ({SkirmishPos.home} : Set SkirmishPos))).trans hstep
end Csg
