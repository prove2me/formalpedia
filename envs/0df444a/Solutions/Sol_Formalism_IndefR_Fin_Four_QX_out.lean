-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.QX_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:43:19.934784+00:00
-- url     : https://prove2.me/submissions/566b8bdc-a88b-478f-8ffb-cdbc18e8d9bd

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
theorem _root_.solution (a : W) : ∃ l ∈ L ⊓ X, (QuotientAddGroup.mk a : QX L X).out = a + l := by
  refine ⟨-a + (QuotientAddGroup.mk a : QX L X).out, ?_, (add_neg_cancel_left a _).symm⟩
  have h : (QuotientAddGroup.mk (QuotientAddGroup.mk a : QX L X).out : QX L X) = QuotientAddGroup.mk a :=
    QuotientAddGroup.out_eq' _
  exact QuotientAddGroup.eq.mp h.symm
end Formalism.IndefR.Fin.Four
