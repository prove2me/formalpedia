-- Prove2me | solution 1 for CompanionTheory.D.Upq.ModEx.exists_modular_function
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:48:36.45215+00:00
-- url     : https://prove2.me/submissions/4b1888b2-c706-40ab-90f7-19486ded33e1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_modProps_modD
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_rightInv_of_modD_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace
open scoped ENNReal NNReal Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.ModEx
open PI PI.QuotSetU.UnitaryGroupMassFormula
variable {m : ℕ}
variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
namespace CompanionTheory.D.Upq.ModEx
theorem _root_.solution : PI.QuotSetU.UnitaryGroupMassFormula.ModExists := fun _ _ hG =>
  ⟨modD hG, modProps_modD hG, rightInv_of_modD_one hG⟩
end CompanionTheory.D.Upq.ModEx
