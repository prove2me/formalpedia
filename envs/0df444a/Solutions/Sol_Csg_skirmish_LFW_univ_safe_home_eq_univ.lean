-- Prove2me | solution 1 for Csg.skirmish_LFW_univ_safe_home_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:13:40.506834+00:00
-- url     : https://prove2.me/submissions/868b2054-64b9-4aab-8ccf-1dc3dc4ed443

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_OrderHom_map_map_bot_le_lfp
import Theorems.Thm_Csg_skirmish_A_safe_home_eq_univ
import Theorems.Thm_Csg_skirmish_B_univ_safe_home_eq_univ
import Theorems.Thm_Csg_CSG_A_univ_v2
import Theorems.Thm_Csg_CSG_B_empty_v1


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.LFW (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe skirmishSafe
        SkirmishPos.home
      = (Set.univ : Set SoldierMove) := by
  apply le_antisymm (Set.subset_univ _)
  have hconst : skirmishCSG.A
      (skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.home)
      skirmishSafe SkirmishPos.home = (Set.univ : Set SoldierMove) := by
    rw [skirmish_B_univ_safe_home_eq_univ, skirmishCSG.A_univ_v2]
  have hbot : skirmishCSG.LFWStep (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe
      skirmishSafe SkirmishPos.home ⊥ = (Set.univ : Set SoldierMove) := by
    change skirmishCSG.A
        (skirmishCSG.B (⊥ : Set SoldierMove) skirmishSafe SkirmishPos.home) skirmishSafe
        SkirmishPos.home ∩
      skirmishCSG.A
        (skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.home) skirmishSafe
        SkirmishPos.home
      = (Set.univ : Set SoldierMove)
    rw [Set.bot_eq_empty, skirmishCSG.B_empty_v1, skirmish_A_safe_home_eq_univ, hconst,
      Set.inter_univ]
  have hstep2 : skirmishCSG.LFWStep (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe
      skirmishSafe SkirmishPos.home
      (skirmishCSG.LFWStep (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe skirmishSafe
        SkirmishPos.home ⊥)
      = (Set.univ : Set SoldierMove) := by
    rw [hbot]
    change skirmishCSG.A
        (skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.home) skirmishSafe
        SkirmishPos.home ∩
      skirmishCSG.A
        (skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.home) skirmishSafe
        SkirmishPos.home
      = (Set.univ : Set SoldierMove)
    rw [hconst, Set.inter_univ]
  exact (le_of_eq hstep2.symm).trans (OrderHom.map_map_bot_le_lfp
    (skirmishCSG.LFWStep (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe skirmishSafe
      SkirmishPos.home))
end Csg
