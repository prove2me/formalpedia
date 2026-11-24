-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.isSB_ind
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:47.722269+00:00
-- url     : https://prove2.me/submissions/1363d31c-f2c7-4634-bb57-3e71580eb232

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {L X : AddSubgroup W}
open Classical
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution : IsSB L X (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) := by
  refine ⟨fun t ht => ?_, 1, one_pos, fun u hu t => ?_, fun t ht => ?_⟩
  · by_contra h
    apply ht
    simp [h]
  · simp only [one_smul, L.add_mem_cancel_right hu.1, X.add_mem_cancel_right hu.2]
  · rw [one_smul]
    by_contra h
    apply ht
    simp [h]
end Formalism.IndefR.Fin.Four
