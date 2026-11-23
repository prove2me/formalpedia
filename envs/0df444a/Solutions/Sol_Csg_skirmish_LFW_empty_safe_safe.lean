-- Prove2me | solution 1 for Csg.skirmish_LFW_empty_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:13:29.378018+00:00
-- url     : https://prove2.me/submissions/ece026f0-0b51-4256-9999-881d46b44b6b

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_CSG_B_empty_x


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : Set SoldierMove) (s : SkirmishPos) :
    skirmishCSG.LFW v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s
      = skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s := by
  have hconst : ∀ W : Set SoldierMove,
      skirmishCSG.LFWStep v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s W
        = skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s := by
    intro W
    change skirmishCSG.A (skirmishCSG.B W (∅ : Set SkirmishPos) s) skirmishSafe s ∩
        skirmishCSG.A (skirmishCSG.B v (∅ : Set SkirmishPos) s) skirmishSafe s
      = skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s
    rw [skirmishCSG.B_empty_x, skirmishCSG.B_empty_x, Set.inter_self]
  apply le_antisymm
  · exact (skirmishCSG.LFWStep v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s).lfp_le
      (le_of_eq (hconst (skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s)))
  · calc skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s
        = skirmishCSG.LFWStep v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s ⊥ :=
          (hconst ⊥).symm
      _ ≤ skirmishCSG.LFWStep v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s
            (skirmishCSG.LFW v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s) :=
          (skirmishCSG.LFWStep v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s).mono bot_le
      _ = skirmishCSG.LFW v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s :=
          (skirmishCSG.LFWStep v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s).map_lfp
end Csg
