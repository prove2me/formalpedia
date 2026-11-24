-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.ext_ops_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:45.897237+00:00
-- url     : https://prove2.me/submissions/23090368-067c-4d26-beb6-0b8652186e21

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_mul
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isL_monomial_ltr
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isF_monomial_frst
import Theorems.Thm_Formalism_CountingSumsFrames_TO_monomial_split
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ops_mul_free
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ops_keep_pred
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
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_add
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
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs] (S : Set σ) (hS : ∀ v ∈ S, ¬ fs v)
    {T : Module.End k (MvPolynomial σ k)} (hT : T ∈ FockB.Ops S)
    (φ : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (hφ : ∀ x, IsF fs (φ x)) (x : MvPolynomial σ k) :
    ext fs φ (T x) = T (ext fs φ x) := by
  have hfree : ∀ g : MvPolynomial σ k, IsF fs g → ∀ m ∈ g.support, ∀ v ∈ S, m v = 0 := by
    intro g hg m hm v hv
    by_contra h
    exact hS v hv (hg m hm v h)
  induction x using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [monomial_split fs m a]
    have hg := isF_monomial_frst (K := k) fs m a
    have hq := isL_monomial_ltr (K := k) fs m 1
    have hTq : IsL fs (T (monomial (ltr fs m) 1)) := ops_keep_pred S (fun v => ¬ fs v) hS hT _ hq
    have e1 : T (monomial (frst fs m) a * monomial (ltr fs m) 1) = monomial (frst fs m) a * T (monomial (ltr fs m) 1) := by
      rw [mul_comm, ops_mul_free S hT _ (hfree _ hg), mul_comm]
    have e2 : T (φ (monomial (frst fs m) a) * monomial (ltr fs m) 1) =
        φ (monomial (frst fs m) a) * T (monomial (ltr fs m) 1) := by
      rw [mul_comm, ops_mul_free S hT _ (hfree _ (hφ _)), mul_comm]
    rw [ext_mul fs φ hg hq, e1, ext_mul fs φ hg hTq, e2]
  | add x y hx hy => simp only [map_add, hx, hy]
end Formalism.CountingSumsFrames.TO
