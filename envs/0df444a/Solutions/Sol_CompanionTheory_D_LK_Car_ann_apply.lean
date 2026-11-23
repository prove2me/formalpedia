-- Prove2me | solution 1 for CompanionTheory.D.LK.Car.ann_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:33.085691+00:00
-- url     : https://prove2.me/submissions/8d460100-9132-4463-8b3e-0b1801517c43

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK CompanionTheory.D.LK.Car
variable {n : ℕ}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace CompanionTheory.D.LK.Car
theorem _root_.solution (i : Pos n) (x : Cn n V) (A : Finset (Pos n)) :
    ann i x A = if i ∈ A then 0 else sg i A • x (insert i A) := rfl
end CompanionTheory.D.LK.Car
