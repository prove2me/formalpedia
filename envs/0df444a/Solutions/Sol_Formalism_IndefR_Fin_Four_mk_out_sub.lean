-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.mk_out_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:36.885245+00:00
-- url     : https://prove2.me/submissions/b19a7990-6b94-408c-8b60-08d070c7ba8e

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq

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
theorem _root_.solution (S : AddSubgroup W) (a : W) : ∃ l ∈ S, (QuotientAddGroup.mk a : W ⧸ S).out = a + l := by
  have h := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (QuotientAddGroup.mk a : W ⧸ S))
  refine ⟨(QuotientAddGroup.mk a : W ⧸ S).out - a, ?_, by abel⟩
  have h2 := S.neg_mem h
  have h3 : -(-(QuotientAddGroup.mk a : W ⧸ S).out + a) = (QuotientAddGroup.mk a : W ⧸ S).out - a := by abel
  rw [h3] at h2
  exact h2
end Formalism.IndefR.Fin.Four
