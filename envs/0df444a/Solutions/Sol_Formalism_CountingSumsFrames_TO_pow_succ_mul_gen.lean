-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.pow_succ_mul_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:25.489407+00:00
-- url     : https://prove2.me/submissions/93d49010-63bf-482e-9a06-14d48f6dbe9e

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_pow_mul_killed
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
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_zero
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
variable {σ : Type} (A : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
  (hA : ∀ a b, A (a * b) = a * A b + b * A a)
include hA
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution {u u' : MvPolynomial σ ℚ_[p]} (hu : A u = u') (hu' : A u' = 0) (k : ℕ) :
    ∀ f, (A ^ (k + 1)) (f * u) = (A ^ (k + 1)) f * u + ((k + 1 : ℕ) : ℚ_[p]) • ((A ^ k) f * u') := by
  induction k with
  | zero =>
    intro f
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, hA, hu, Nat.cast_one, one_smul]
    ring
  | succ k ih =>
    intro f
    have e1 : (A ^ (k + 1 + 1)) (f * u) = (A ^ (k + 1)) (A (f * u)) := by
      rw [pow_succ A (k + 1), Module.End.mul_apply]
    have e2 : (A ^ (k + 1 + 1)) f = (A ^ (k + 1)) (A f) := by
      rw [pow_succ A (k + 1), Module.End.mul_apply]
    have e3 : (A ^ (k + 1)) f = (A ^ k) (A f) := by
      rw [pow_succ A k, Module.End.mul_apply]
    rw [e1, e2, hA, hu, map_add, pow_mul_killed A hA hu' (k + 1), mul_comm u, ih, ← e3,
      Nat.cast_succ (k + 1), add_smul, one_smul]
    abel
end Formalism.CountingSumsFrames.TO
