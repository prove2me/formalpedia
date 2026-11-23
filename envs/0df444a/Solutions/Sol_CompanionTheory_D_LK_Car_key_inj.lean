-- Prove2me | solution 1 for CompanionTheory.D.LK.Car.key_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:57.201874+00:00
-- url     : https://prove2.me/submissions/5e7767c5-f03d-450a-afb7-a8ba694f8649

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
theorem _root_.solution {i j : Pos n} (h : key i = key j) : i = j := by
  unfold key at h
  have hi := i.1.2.2
  have hj := j.1.2.2
  have hn : 0 < n := by omega
  have h2 : (i.1.2 : ℕ) = j.1.2 := by
    have := congrArg (· % n) h
    simpa [Nat.mul_add_mod_of_lt hi, Nat.mul_add_mod_of_lt hj] using this
  have h1 : (i.1.1 : ℕ) = j.1.1 := by
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_right hn (Nat.add_right_cancel h)
  exact Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))
end CompanionTheory.D.LK.Car
