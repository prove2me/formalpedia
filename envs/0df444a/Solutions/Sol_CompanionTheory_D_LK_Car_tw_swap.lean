-- Prove2me | solution 1 for CompanionTheory.D.LK.Car.tw_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:22.831998+00:00
-- url     : https://prove2.me/submissions/94b46dfc-57f8-4462-9f49-2a194eb9b93f

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Theorems.Thm_CompanionTheory_D_LK_Car_key_inj
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK CompanionTheory.D.LK.Car
variable {n : ℕ}
namespace CompanionTheory.D.LK.Car
theorem _root_.solution {i j : Pos n} (h : i ≠ j) : tw j i = -tw i j := by
  have hk : key i ≠ key j := fun e => h (key_inj e)
  unfold tw
  rcases lt_or_gt_of_ne hk with h1 | h1
  · simp [h1, h1.not_gt]
  · simp [h1, h1.not_gt]
end CompanionTheory.D.LK.Car
