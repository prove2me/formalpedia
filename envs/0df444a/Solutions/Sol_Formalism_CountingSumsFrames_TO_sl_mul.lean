-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.sl_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:12.63382+00:00
-- url     : https://prove2.me/submissions/174e53a5-983c-4e37-b359-c3fe7a34178d

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_frst_of
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ltr_of
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_frst_of__a64a2b7f77bf
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_ltr_of__5656358b1af2
import Theorems.Thm_Formalism_CountingSumsFrames_TO_frst_add
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ltr_add
import Theorems.Thm_Formalism_CountingSumsFrames_TO_sl_monomial
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
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (m : σ →₀ ℕ) {g q : MvPolynomial σ K} (hg : IsF fs g) (hq : IsL fs q) :
    slc fs m (g * q) = coeff m q • g := by
  classical
  conv_lhs => rw [g.as_sum, q.as_sum, Finset.sum_mul_sum, map_sum]
  conv_rhs => rw [g.as_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [map_sum]
  have key : ∀ b ∈ q.support, slc fs m (monomial a (coeff a g) * monomial b (coeff b q)) =
      if b = m then monomial a (coeff a g * coeff m q) else 0 := by
    intro b hb
    rw [monomial_mul, sl_monomial, frst_add, ltr_add, frst_of fs (hg a ha), ltr_of fs (hg a ha),
      frst_of' fs (hq b hb), ltr_of' fs (hq b hb), add_zero, zero_add]
    split_ifs with h
    · rw [h]
    · rfl
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with hm
  · rw [smul_monomial, smul_eq_mul, mul_comm (coeff a g)]
  · simp only [mem_support_iff, not_not] at hm
    rw [hm, zero_smul]
end Formalism.CountingSumsFrames.TO
