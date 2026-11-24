-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.ext_glAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:38.588449+00:00
-- url     : https://prove2.me/submissions/1164357b-7512-4c8d-8db1-962a32f95eab

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_mul
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isL_monomial_ltr
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isF_monomial_frst
import Theorems.Thm_Formalism_CountingSumsFrames_TO_monomial_split
import Theorems.Thm_Formalism_CountingSumsFrames_TO_glAct_isF
import Theorems.Thm_Formalism_CountingSumsFrames_TO_killL_of_isL
import Theorems.Thm_Formalism_CountingSumsFrames_TO_midAct_isL
import Theorems.Thm_Formalism_CountingSumsFrames_TO_midAct_mul_F
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_mul_kill
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_split
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
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφ1 : ∀ c d x, φ (glAct p L j0 c d x) = glAct p L j0 c d (φ x)) (hφF : ∀ x, IsF (fsj N r j0) (φ x))
    (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ext (fsj N r j0) φ (glAct p L J c d x) = glAct p L J c d (ext (fsj N r j0) φ x) := by
  induction x using MvPolynomial.induction_on' with
  | monomial m' a =>
    have hg := isF_monomial_frst (fsj N r j0) m' a
    have hq := isL_monomial_ltr (fsj N r j0) m' (1 : ℚ_[p])
    rw [monomial_split (fsj N r j0) m' a, ext_mul _ φ hg hq, glAct_split L hJ c d, LinearMap.add_apply,
      LinearMap.add_apply, glAct_mul_kill L j0 c d _ (killL_of_isL le_rfl hq), midAct_mul_F L hJ c d hg,
      glAct_mul_kill L j0 c d _ (killL_of_isL le_rfl hq), midAct_mul_F L hJ c d (hφF _), map_add,
      ext_mul _ φ (glAct_isF L j0 j0 c d hg) hq, ext_mul _ φ hg (midAct_isL L hJ c d hq), hφ1]
  | add x y hx hy => simp only [map_add, hx, hy]
end Formalism.CountingSumsFrames.TO
