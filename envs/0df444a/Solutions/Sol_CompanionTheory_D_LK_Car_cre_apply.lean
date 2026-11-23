-- Prove2me | solution 1 for CompanionTheory.D.LK.Car.cre_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:39.430432+00:00
-- url     : https://prove2.me/submissions/dff2daaf-3daa-4018-886f-30c9a2831974

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
    cre i x A = if i ∈ A then sg i A • x (A.erase i) else 0 := rfl
end CompanionTheory.D.LK.Car
