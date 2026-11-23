-- Prove2me | solution 1 for Csg.skirmish_B_univ_safe_hide_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:13:00.272203+00:00
-- url     : https://prove2.me/submissions/28faf71f-fdc9-4636-a1aa-dc73598c51c2

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_B_singleton_hide_safe_hide_eq_univ

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.hide
      = (Set.univ : Set SniperMove) := by
  apply le_antisymm (Set.subset_univ _)
  calc (Set.univ : Set SniperMove)
      = skirmishCSG.B ({SoldierMove.hide} : Set SoldierMove) skirmishSafe SkirmishPos.hide :=
        skirmish_B_singleton_hide_safe_hide_eq_univ.symm
    _ ≤ skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.hide :=
        skirmishCSG.B_mono_v1 skirmishSafe
          (Set.subset_univ ({SoldierMove.hide} : Set SoldierMove)) SkirmishPos.hide
end Csg
