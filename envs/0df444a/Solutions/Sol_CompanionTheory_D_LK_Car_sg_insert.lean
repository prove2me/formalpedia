-- Prove2me | solution 1 for CompanionTheory.D.LK.Car.sg_insert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:59.054801+00:00
-- url     : https://prove2.me/submissions/daae02b7-086f-4a0f-b6fe-b6642b5a998c

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
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
theorem _root_.solution (i : Pos n) {j : Pos n} {A : Finset (Pos n)} (h : j ∉ A) :
    sg i (insert j A) = tw i j * sg i A := by
  unfold sg tw
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp
end CompanionTheory.D.LK.Car
