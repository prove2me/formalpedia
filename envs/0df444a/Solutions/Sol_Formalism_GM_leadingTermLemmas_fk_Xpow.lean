-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_Xpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:53.249555+00:00
-- url     : https://prove2.me/submissions/e9303947-9f1b-405b-a8a0-e41abf9e317a

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_eq_sum
import Theorems.Thm_Formalism_GM_leadingTermLemmas_wf_single_add
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
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (i : σ) (k : ℕ) (g g' : MvPolynomial σ K) :
    fk (X i ^ k * g) (X i ^ k * g') =
      ∑ M ∈ g.support, g.coeff M * g'.coeff M * wf M * (((M i + k).descFactorial k : ℕ) : K) := by
  classical
  have hX : (X i ^ k : MvPolynomial σ K) = monomial (Finsupp.single i k) 1 := by rw [X_pow_eq_monomial]
  have hs : (X i ^ k * g).support ⊆ g.support.map (addLeftEmbedding (Finsupp.single i k)) := by
    intro M hM
    have := support_mul (X i ^ k) g hM
    rw [hX, support_monomial, if_neg one_ne_zero] at this
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp this
    simp only [Finset.mem_singleton] at ha
    subst ha
    exact Finset.mem_map.mpr ⟨b, hb, rfl⟩
  rw [fk_eq_sum _ _ _ hs, Finset.sum_map]
  refine Finset.sum_congr rfl (fun M _ => ?_)
  simp only [addLeftEmbedding_apply, hX, coeff_monomial_mul, one_mul, wf_single_add]
  ring
end Formalism.GM.leadingTermLemmas
