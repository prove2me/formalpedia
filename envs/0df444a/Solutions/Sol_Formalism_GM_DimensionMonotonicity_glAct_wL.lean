-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.glAct_wL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:08.388823+00:00
-- url     : https://prove2.me/submissions/961b81f9-a544-4e3f-b906-7b4d5ddd4840

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (a b : Fin r) {D : Fin N → ℤ} {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wL N r) D) :
    glAct p LL j a b x ∈ weightedHomogeneousSubmodule ℚ_[p] (wL N r) D := by
  rw [mem_weightedHomogeneousSubmodule] at hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hwd : Finsupp.weight (wL N r) d = D := hx (mem_support_iff.mp hd)
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h1 h2
  · have h3 := wh_XD (K := ℚ_[p]) (wL N r) (i, b) (i, a) d (coeff d x)
    have e : D = Finsupp.weight (wL N r) d - wL N r (i, b) + wL N r (i, a) := by
      rw [hwd]
      simp [wL]
    rw [e]
    exact h3
  · have h3 := wh_XD (K := ℚ_[p]) (wL N r) (i, a) (i, b) d (coeff d x)
    have e : D = Finsupp.weight (wL N r) d - wL N r (i, a) + wL N r (i, b) := by
      rw [hwd]
      simp [wL]
    rw [LinearMap.neg_apply, e]
    exact Submodule.neg_mem _ h3
  · rw [LinearMap.zero_apply]
    exact Submodule.zero_mem _
end Formalism.GM.DimensionMonotonicity
