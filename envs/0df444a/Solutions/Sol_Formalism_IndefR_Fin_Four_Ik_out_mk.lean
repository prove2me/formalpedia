-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.Ik_out_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:17.622898+00:00
-- url     : https://prove2.me/submissions/621ae2db-e61a-43ff-adfd-1b53cf393736

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac
import Theorems.Thm_Formalism_IndefR_Fin_Four_mem_smulSub


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
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {L Y : AddSubgroup W} {k : ℕ} (z : Yk L Y k) :
    ∃ v ∈ L ⊓ Y, ((((QuotientAddGroup.mk z : Ik L Y k)).out : ↥(Yk L Y k)) : W) + k • v = (z : W) := by
  have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk z : Ik L Y k))
  rw [AddSubgroup.mem_addSubgroupOf] at h
  obtain ⟨v, hv, hvx⟩ := mem_smulSub.1 h
  refine ⟨v, hv, ?_⟩
  rw [hvx]
  push_cast
  abel
end Formalism.IndefR.Fin.Four
