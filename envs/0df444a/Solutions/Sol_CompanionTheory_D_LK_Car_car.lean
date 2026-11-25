-- Prove2me | solution 1 for CompanionTheory.D.LK.Car.car
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:16:15.415849+00:00
-- url     : https://prove2.me/submissions/829d8d28-4569-42e5-8953-fd78804f1284

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Theorems.Thm_CompanionTheory_D_LK_Car_ann_ann
import Theorems.Thm_CompanionTheory_D_LK_Car_cre_cre
import Theorems.Thm_CompanionTheory_D_LK_Car_ann_cre

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
theorem _root_.solution : CARp := fun _ _ _ _ i j => ⟨ann_ann i j, cre_cre i j, ann_cre i j⟩
end CompanionTheory.D.LK.Car
