-- Prove2me | solution 1 for Csg.skirmish_hide_not_mem_AGF_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:47.021804+00:00
-- url     : https://prove2.me/submissions/c4f40d76-971a-4a4e-aafd-d322506723d6

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_AGF_home_le_home

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.hide ∉ skirmishCSG.AGF ({SkirmishPos.home} : Set SkirmishPos) := by
  intro hmem
  exact absurd (Set.eq_of_mem_singleton (skirmish_AGF_home_le_home hmem)) (by decide)
end Csg
