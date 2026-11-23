-- Prove2me | solution 1 for Csg.skirmish_LW_home_safe_hide_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:13:03.192786+00:00
-- url     : https://prove2.me/submissions/63e94152-5a75-4bfb-8a03-c1fe9ccf692f

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_OrderHom_map_map_bot_le_lfp
import Theorems.Thm_Csg_skirmish_hide_mem_A_safe_hide
import Theorems.Thm_Csg_skirmish_throw_mem_B_singleton_hide_home
import Theorems.Thm_Csg_skirmish_univ_subset_A_throw_safe_hide
import Theorems.Thm_Csg_CSG_B_empty_v1


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.LW ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe SkirmishPos.hide
      = (Set.univ : Set SoldierMove) := by
  apply le_antisymm (Set.subset_univ _)
  have hbot : skirmishCSG.LStep ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      SkirmishPos.hide ⊥ = skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide := by
    change skirmishCSG.A
        (skirmishCSG.B (⊥ : Set SoldierMove) ({SkirmishPos.home} : Set SkirmishPos)
          SkirmishPos.hide)
        skirmishSafe SkirmishPos.hide
      = skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide
    rw [Set.bot_eq_empty, skirmishCSG.B_empty_v1]
  have hthrow_mem : SniperMove.throw ∈ skirmishCSG.B
      (skirmishCSG.LStep ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        SkirmishPos.hide ⊥)
      ({SkirmishPos.home} : Set SkirmishPos) SkirmishPos.hide := by
    rw [hbot]
    exact skirmishCSG.B_mono_v1 _
      (Set.singleton_subset_iff.mpr skirmish_hide_mem_A_safe_hide) _
      skirmish_throw_mem_B_singleton_hide_home
  have hffbot : (Set.univ : Set SoldierMove) ⊆
      skirmishCSG.LStep ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe SkirmishPos.hide
        (skirmishCSG.LStep ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
          SkirmishPos.hide ⊥) := by
    change (Set.univ : Set SoldierMove) ⊆ skirmishCSG.A
        (skirmishCSG.B
          (skirmishCSG.LStep ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
            SkirmishPos.hide ⊥)
          ({SkirmishPos.home} : Set SkirmishPos) SkirmishPos.hide)
        skirmishSafe SkirmishPos.hide
    exact skirmish_univ_subset_A_throw_safe_hide.trans
      (skirmishCSG.A_mono_v2 skirmishSafe (Set.singleton_subset_iff.mpr hthrow_mem) _)
  exact hffbot.trans (OrderHom.map_map_bot_le_lfp
    (skirmishCSG.LStep ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe SkirmishPos.hide))
end Csg
