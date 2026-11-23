-- Prove2me | solution 1 for Csg.skirmish_A_safe_home_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:08:36.887432+00:00
-- url     : https://prove2.me/submissions/3f1e256d-bedc-4420-b36e-f50b0ff03d02

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishK_support_home


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.home = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a1 a2
  right
  rw [skirmishK_support_home]
  exact Set.singleton_subset_iff.mpr (by decide)
end Csg
