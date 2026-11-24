-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.exists_pow_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:36.889952+00:00
-- url     : https://prove2.me/submissions/daa9c69b-45df-463c-8a0a-4020d03d180d

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_smul_int
import Theorems.Thm_Formalism_CountingSumsFrames_TO_norm_p_pow_le
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
import Theorems.Thm_Formalism_GM_TM_mem_intPol_of_norm
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_congr
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_congr
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
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution {σ : Type} (v : MvPolynomial σ ℚ_[p]) : ∃ k : ℕ, ((p : ℚ_[p]) ^ k) • v ∈ IntPol p σ := by
  classical
  induction v using MvPolynomial.induction_on' with
  | monomial m a =>
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖a‖ hp1
    refine ⟨k, mem_intPol_of_norm _ fun m' => ?_⟩
    rw [coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs
    · rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
      rw [inv_mul_le_iff₀ (by positivity), mul_one]
      exact hk.le
    · simp
  | add x y hx hy =>
    obtain ⟨k1, h1⟩ := hx
    obtain ⟨k2, h2⟩ := hy
    refine ⟨k1 + k2, ?_⟩
    have e : ((p : ℚ_[p]) ^ (k1 + k2)) • (x + y) =
        ((p : ℚ_[p]) ^ k2) • (((p : ℚ_[p]) ^ k1) • x) + ((p : ℚ_[p]) ^ k1) • (((p : ℚ_[p]) ^ k2) • y) := by
      rw [smul_add, smul_smul, smul_smul, pow_add]
      congr 2; ring
    rw [e]
    exact Submodule.add_mem _ (smul_int (norm_p_pow_le k2) h1) (smul_int (norm_p_pow_le k1) h2)
end Formalism.CountingSumsFrames.TO
