-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.hwc_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:52.850158+00:00
-- url     : https://prove2.me/submissions/3e72d405-bd56-46ca-99e7-0bff12a2fa1d

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_E
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_enumC_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_enumC_surj
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_wtSpC_iff
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ HWC p LL j Cs la ↔ (GAe p LL j (enumC Cs)).IsHW (la ∘ enumC Cs) x := by
  unfold HWC GlW.IsHW
  rw [Submodule.mem_inf, wtSpC_iff]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, GAe_E]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h a b hab
    exact h _ _ ⟨enumC_mem Cs a, enumC_mem Cs b, (enumC Cs).lt_iff_lt.mpr hab⟩
  · rintro h c d ⟨hc, hd, hcd⟩
    obtain ⟨a, rfl⟩ := enumC_surj Cs hc
    obtain ⟨b, rfl⟩ := enumC_surj Cs hd
    exact h a b ((enumC Cs).lt_iff_lt.mp hcd)
end Formalism.InvariantFactorPaths.PW
