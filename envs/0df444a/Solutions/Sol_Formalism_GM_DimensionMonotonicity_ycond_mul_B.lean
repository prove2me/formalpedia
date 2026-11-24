-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.ycond_mul_B
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:16.333362+00:00
-- url     : https://prove2.me/submissions/53fde91b-1a55-435b-b048-bd53d85d796c

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_mul_kill
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_of_comm
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
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution [NeZero r] (LL : Letters N) {J j0 : ℕ} (hJ : J ≤ j0) (M : WithTop ℤ)
    {q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hq : ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → m v = 0) :
    ∀ F ∈ YCond p LL J M, q * F ∈ YCond p LL J M := by
  refine ycond_of_comm LL J M (LinearMap.mulLeft ℚ_[p] q) ?_ ?_
  · intro c d G
    simp only [LinearMap.mulLeft_apply]
    rw [mul_comm q, mul_comm q, glAct_mul_kill LL J c d G (fun m hm v hv => hq m hm v (by omega))]
  · intro ν G hG
    simp only [LinearMap.mulLeft_apply]
    have hq0 : q ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) 0 := by
      rw [mem_weightedHomogeneousSubmodule]
      intro m hm
      rw [Finsupp.weight_apply, Finsupp.sum]
      refine Finset.sum_eq_zero fun v _ => ?_
      by_cases h : (v.1 : ℕ) < J
      · rw [hq m (mem_support_iff.mpr hm) v (by omega), zero_smul]
      · simp [wv, h]
    rw [mem_weightedHomogeneousSubmodule] at hG hq0 ⊢
    have h5 := hq0.mul hG
    rwa [zero_add] at h5
end Formalism.GM.DimensionMonotonicity
