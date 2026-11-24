-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ext_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:35.270801+00:00
-- url     : https://prove2.me/submissions/ba4994f7-5d50-4c54-8436-8449cdf87f8f

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_frst_of
import Theorems.Thm_Formalism_CountingSumsFrames_ltr_of
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_frst_of__97055c5e3784
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_ltr_of__7102e4470fc7
import Theorems.Thm_Formalism_CountingSumsFrames_frst_add
import Theorems.Thm_Formalism_CountingSumsFrames_ltr_add
import Theorems.Thm_Formalism_CountingSumsFrames_ext_monomial
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
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
namespace Formalism.CountingSumsFrames
theorem _root_.solution (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) {g q : MvPolynomial σ K} (hg : IsF fs g)
    (hq : IsL fs q) : ext fs φ (g * q) = φ g * q := by
  rw [g.as_sum, q.as_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun m' hm' => Finset.sum_congr rfl fun m hm => ?_
  rw [MvPolynomial.monomial_mul, ext_monomial, frst_add, ltr_add, frst_of fs (hg m hm), frst_of' fs (hq m' hm'),
    ltr_of fs (hg m hm), ltr_of' fs (hq m' hm'), add_zero, zero_add,
    show monomial m (coeff m g) = coeff m g • monomial m (1 : K) by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
    map_smul,
    show monomial m' (coeff m' q) = coeff m' q • monomial m' (1 : K) by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
    smul_mul_smul_comm]
end Formalism.CountingSumsFrames
