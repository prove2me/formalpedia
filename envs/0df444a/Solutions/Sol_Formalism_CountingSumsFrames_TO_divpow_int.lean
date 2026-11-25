-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.divpow_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:55.000644+00:00
-- url     : https://prove2.me/submissions/bb04b1d6-9ba3-42e5-9ab0-3529f5919fef

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_pow_succ_mul_gen
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_glAct_C__b6e3a9844982
import Theorems.Thm_Formalism_CountingSumsFrames_TO_glAct_X_int
import Theorems.Thm_Formalism_CountingSumsFrames_TO_glAct_glAct_X
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_X
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_iff
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_mul
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_glAct_mul
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_zero
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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (L : Letters N) (j : ℕ) (c d : Fin r) (hcd : c ≠ d) (k : ℕ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ IntPol p (Fin N × Fin r)) :
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p L j c d) ^ k) x ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨x₀, rfl⟩ := (FrozenVariableLemmas.intPol_iff p x).mp hx
  clear hx
  induction x₀ using MvPolynomial.induction_on generalizing k with
  | C a =>
    rw [map_C]
    cases k with
    | zero => simpa using (FrozenVariableLemmas.intPol_iff p _).mpr ⟨C a, map_C _ _⟩
    | succ k =>
      rw [pow_succ, Module.End.mul_apply, glAct_C', map_zero, smul_zero]
      exact Submodule.zero_mem _
  | add f g hf hg =>
    rw [map_add, map_add, smul_add]
    exact Submodule.add_mem _ (hf k) (hg k)
  | mul_X f v hf =>
    rw [map_mul, map_X]
    cases k with
    | zero =>
      have := hf 0
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply, one_smul] at this ⊢
      exact FrozenVariableLemmas.intPol_mul p this (FrozenVariableLemmas.intPol_X p v)
    | succ k =>
      rw [pow_succ_mul_gen (glAct p L j c d) (fun a b => Formalism.GM.M.FB.glAct_mul L j c d a b) rfl
        (glAct_glAct_X L j c d hcd v) k, smul_add, smul_smul]
      have e : (((k + 1).factorial : ℚ_[p]))⁻¹ * ((k + 1 : ℕ) : ℚ_[p]) = ((k.factorial : ℚ_[p]))⁻¹ := by
        have h1 : ((k + 1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        have h2 : ((k.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
        rw [Nat.factorial_succ, Nat.cast_mul]
        field_simp
      rw [e, ← smul_mul_assoc, ← smul_mul_assoc]
      exact Submodule.add_mem _ (FrozenVariableLemmas.intPol_mul p (hf (k + 1)) (FrozenVariableLemmas.intPol_X p v))
        (FrozenVariableLemmas.intPol_mul p (hf k) (glAct_X_int L j c d v))
end Formalism.CountingSumsFrames.TO
