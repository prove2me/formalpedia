-- Prove2me | solution 1 for CompanionTheory.D.LK.Car.sg_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:59.043734+00:00
-- url     : https://prove2.me/submissions/3a51681b-2c92-4037-a42d-46cbd7401064

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
theorem _root_.solution (i : Pos n) (A : Finset (Pos n)) : sg i A * sg i A = 1 := by
  unfold sg
  rw [← mul_pow]; simp
end CompanionTheory.D.LK.Car
