-- Prove2me | solution 1 for Formalism.CountingSumsFrames.sl_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:45.404739+00:00
-- url     : https://prove2.me/submissions/f7f84608-77c0-41dc-bd7c-144b7f92d4f6

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_frst_of
import Theorems.Thm_Formalism_CountingSumsFrames_ltr_of
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_frst_of__97055c5e3784
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_ltr_of__7102e4470fc7
import Theorems.Thm_Formalism_CountingSumsFrames_frst_add
import Theorems.Thm_Formalism_CountingSumsFrames_ltr_add
import Theorems.Thm_Formalism_CountingSumsFrames_sl_monomial
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
theorem _root_.solution (m : σ →₀ ℕ) {g q : MvPolynomial σ K} (hg : IsF fs g) (hq : IsL fs q) :
    slc fs m (g * q) = coeff m q • g := by
  conv_lhs => rw [g.as_sum, q.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
  have key : ∀ a ∈ g.support, ∀ b ∈ q.support,
      slc fs m (monomial a (coeff a g) * monomial b (coeff b q)) = if b = m then coeff m q • monomial a (coeff a g) else 0 := by
    intro a ha b hb
    rw [MvPolynomial.monomial_mul, sl_monomial, frst_add, ltr_add, frst_of fs (hg a ha), frst_of' fs (hq b hb),
      ltr_of fs (hg a ha), ltr_of' fs (hq b hb), add_zero, zero_add]
    split_ifs with h
    · subst h
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
    · rfl
  rw [Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => key a ha b hb, Finset.sum_comm]
  by_cases hm : m ∈ q.support
  · simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, hm, if_true]
    rw [← Finset.smul_sum, ← g.as_sum]
  · have h0 : coeff m q = 0 := by simpa using hm
    simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, hm, if_false, Finset.sum_const_zero, h0, zero_smul]
end Formalism.CountingSumsFrames
