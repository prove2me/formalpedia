-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.isSB_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:00.927444+00:00
-- url     : https://prove2.me/submissions/e02d7f47-3586-4878-ad21-60353ef8a87b

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
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution : IsSB L X (0 : W → ℂ) :=
  ⟨fun t h => absurd rfl h, 1, one_pos, fun _ _ _ => rfl, fun t h => absurd rfl h⟩
end Formalism.IndefR.Fin.Four
