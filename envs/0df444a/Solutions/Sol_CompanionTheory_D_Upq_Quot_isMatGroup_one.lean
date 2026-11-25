-- Prove2me | solution 1 for CompanionTheory.D.Upq.Quot.isMatGroup_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:24:05.955609+00:00
-- url     : https://prove2.me/submissions/e4286738-af81-40ec-9347-46852ae50123

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_QuotientMeasureUnitaryGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_ExistsQuotientMeasureUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Quot
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula CompanionTheory.D.Upq.ModEx
variable {m : ℕ}
namespace CompanionTheory.D.Upq.Quot
theorem _root_.solution : IsMatGroup ({1} : Set (Matrix (Fin m) (Fin m) ℂ)) :=
  ⟨isClosed_singleton, rfl, fun a ha b hb => by
    rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]; simp, fun a ha => by
    rw [Set.mem_singleton_iff.1 ha]; simp⟩
end CompanionTheory.D.Upq.Quot
