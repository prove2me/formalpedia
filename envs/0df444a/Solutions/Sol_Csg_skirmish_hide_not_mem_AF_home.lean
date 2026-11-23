-- Prove2me | solution 1 for Csg.skirmish_hide_not_mem_AF_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:31.686896+00:00
-- url     : https://prove2.me/submissions/06c2f6d8-fc17-4300-9a9b-4248c1d1aa4d

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_AF_home_le_home

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.hide ∉ skirmishCSG.AF ({SkirmishPos.home} : Set SkirmishPos) := by
  intro hmem
  exact absurd (Set.eq_of_mem_singleton (skirmish_AF_home_le_home hmem)) (by decide)
end Csg
