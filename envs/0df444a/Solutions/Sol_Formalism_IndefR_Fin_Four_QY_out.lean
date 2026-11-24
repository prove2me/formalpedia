-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.QY_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:43:08.375575+00:00
-- url     : https://prove2.me/submissions/fce5c487-9cf5-4862-bca4-a2d8632c9a76

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel

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
variable {L X Y : AddSubgroup W}
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (y : W) : ∃ μ ∈ L ⊓ Y, (QuotientAddGroup.mk y : QY L Y).out = y + μ := by
  refine ⟨-y + (QuotientAddGroup.mk y : QY L Y).out, ?_, (add_neg_cancel_left y _).symm⟩
  have h : (QuotientAddGroup.mk (QuotientAddGroup.mk y : QY L Y).out : QY L Y) = QuotientAddGroup.mk y :=
    QuotientAddGroup.out_eq' _
  exact QuotientAddGroup.eq.mp h.symm
end Formalism.IndefR.Fin.Four
