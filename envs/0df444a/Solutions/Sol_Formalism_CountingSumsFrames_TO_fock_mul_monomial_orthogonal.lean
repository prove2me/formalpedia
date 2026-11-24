-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.fock_mul_monomial_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:06.501532+00:00
-- url     : https://prove2.me/submissions/85408b7a-4151-4549-ac5d-b16b7eeb1186

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_wf_add_disj
import Theorems.Thm_Formalism_CountingSumsFrames_TO_add_eq_add_iff_disj
import Theorems.Thm_Formalism_CountingSumsFrames_fock_monomial
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
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_prod
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_prod
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_monomial
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_sum_left
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_sum_right
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_prod_eq_wf
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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (j0 : ℕ) (s t : Finset (Fin N × Fin r →₀ ℕ)) (cg cg' : (Fin N × Fin r →₀ ℕ) → ℚ_[p])
    (hs : ∀ a ∈ s, ∀ v, a v ≠ 0 → fsj N r j0 v) (ht : ∀ b ∈ t, ∀ v, b v ≠ 0 → fsj N r j0 v)
    (m m' : Fin N × Fin r →₀ ℕ) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) :
    fock p ((∑ a ∈ s, monomial a (cg a)) * monomial m 1) ((∑ b ∈ t, monomial b (cg' b)) * monomial m' 1) =
      if m = m' then fock p (∑ a ∈ s, monomial a (cg a)) (∑ b ∈ t, monomial b (cg' b)) *
        (m.prod fun _ k => (k.factorial : ℚ_[p])) else 0 := by
  rw [Finset.sum_mul, Finset.sum_mul, gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.prod_eq_wf]
  simp only [gammaIntegralityLemmas.fock_sum_right, monomial_mul, mul_one, gammaIntegralityLemmas.fock_monomial]
  by_cases hmm : m = m'
  · rw [if_pos hmm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b hb => ?_
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (by rw [hab, hmm]), wf_add_disj j0 a m (hs a ha) hm]; ring
    · rw [if_neg hab, if_neg (fun h => hab ((add_eq_add_iff_disj j0 a b m m' (hs a ha) (ht b hb) hm hm').mp h).1),
        zero_mul]
  · rw [if_neg hmm]
    refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
    rw [if_neg (fun h => hmm ((add_eq_add_iff_disj j0 a b m m' (hs a ha) (ht b hb) hm hm').mp h).2)]
end Formalism.CountingSumsFrames.TO
