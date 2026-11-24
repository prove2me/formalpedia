-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.midAct_wh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:25.750693+00:00
-- url     : https://prove2.me/submissions/cbb20ee7-c0eb-4ae1-ae65-57989c441d3b

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
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
theorem _root_.solution (LL : Letters N) (J j0 : ℕ) (c d : Fin r) {ν : Fin r → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν) :
    midAct p LL J j0 c d x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν := by
  rw [mem_weightedHomogeneousSubmodule] at hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hwd : Finsupp.weight (wv LL J) m = ν := hx (mem_support_iff.mp hm)
  unfold midAct Formalism.GM.FrozenVariableComponents.top
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h1 h2
  · have hnJ : ¬ ((i : ℕ) < J) := by omega
    have h3 := wh_XD (K := ℚ_[p]) (wv LL J) (i, d) (i, c) m (coeff m x)
    have e : ν = Finsupp.weight (wv LL J) m - wv LL J (i, d) + wv LL J (i, c) := by
      rw [hwd]
      simp [wv, hnJ]
    rw [e]
    exact h3
  · have hnJ : ¬ ((i : ℕ) < J) := by omega
    have h3 := wh_XD (K := ℚ_[p]) (wv LL J) (i, c) (i, d) m (coeff m x)
    have e : ν = Finsupp.weight (wv LL J) m - wv LL J (i, c) + wv LL J (i, d) := by
      rw [hwd]
      simp [wv, hnJ]
    rw [LinearMap.neg_apply, e]
    exact Submodule.neg_mem _ h3
  · rw [LinearMap.zero_apply]
    exact Submodule.zero_mem _
end Formalism.GM.DimensionMonotonicity
