-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx1.t_PSDAgree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:14.412358+00:00
-- url     : https://prove2.me/submissions/72948742-71ed-44e8-8533-68e98444c706

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_conv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_t_PSDTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_q_im
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_ta_to_tb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_psd_form_conj_rewrite
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_psd_kernel_hermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.Jx1
theorem _root_.solution : PSDAgree := by
  unfold PSDAgree
  intro α F k
  refine ⟨⟨fun h => conv F _ (t_PSDTranspose α F k h), ta_to_tb F k⟩, ⟨fun h => ⟨psd_kernel_hermitian F k h, fun a => ?_⟩, fun h => ?_⟩⟩
  · have h2 := (h (fun z => conj (a z))).2
    refine le_of_le_of_eq h2 ?_
    congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [Complex.conj_conj]
    ring
  · intro a
    rw [psd_form_conj_rewrite F k a]
    exact ⟨q_im F k h.1 _, h.2 _⟩
end Formalism.FourierDecayAlt.P.Jx1
