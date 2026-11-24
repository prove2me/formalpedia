-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.glAct_freezeSub_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:39.139392+00:00
-- url     : https://prove2.me/submissions/3e685c97-ba5d-4b43-84d6-fad1cd0c7394

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_vec_last
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_snoc_vec_last
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_glAct_X
import Theorems.Thm_Formalism_GM_M_FB_glAct_mul
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
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
open Formalism.GM.M.FB
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (LL : Letters K) (n : ℕ) (ρ a b : Fin r) (ha : a ≠ ρ) (hb : b ≠ ρ)
    (v : Fin K × Fin r) :
    glAct p (LL.snoc n) (K + 1) a b (freezeSub p LL ρ v) = aeval (freezeSub p LL ρ) (glAct p LL K a b (X v)) := by
  classical
  obtain ⟨i, c'⟩ := v
  rw [glAct_X]
  by_cases h1 : LL.vec i
  · by_cases h2 : c' = ρ
    · subst h2
      simp only [freezeSub, h1, if_true, map_sum, glAct_mul, glAct_X, snoc_vec_last, snoc_vec_castSucc]
      simp [mul_ite, Finset.sum_add_distrib, ha, hb, Ne.symm hb, Ne.symm ha]
      try ring
    · simp only [freezeSub, h1, h2, if_true, if_false, glAct_mul, glAct_X, snoc_vec_last, snoc_vec_castSucc]
      by_cases h3 : c' = b
      · subst h3; simp [h2, Ne.symm h2, ha, Ne.symm ha, freezeSub, h1]; try ring
      · simp [h2, Ne.symm h2, h3, ha, Ne.symm ha]
  · by_cases h2 : c' = ρ
    · subst h2
      simp only [freezeSub, h1, if_true, if_false, Bool.false_eq_true, glAct_mul, glAct_X, snoc_vec_last,
        snoc_vec_castSucc]
      simp [ha, Ne.symm ha]
    · simp only [freezeSub, h1, h2, if_true, if_false, Bool.false_eq_true, glAct_mul, glAct_X, snoc_vec_last,
        snoc_vec_castSucc, map_sub]
      by_cases h3 : c' = a
      · subst h3; simp [h2, Ne.symm h2, hb, Ne.symm hb, freezeSub, h1]; try ring
      · simp [h2, Ne.symm h2, h3, ha, Ne.symm ha]
end Formalism.GM.DimensionMonotonicity
