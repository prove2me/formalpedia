-- Prove2me | solution 1 for Formalism.CountingSumsFrames.wt_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:48.581799+00:00
-- url     : https://prove2.me/submissions/3f569b41-acd8-4bdd-af8c-b4bd7dcfeca1

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
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
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters K) (n : ℕ) (ρ c : Fin r) (m' : Fin K × Fin r →₀ ℕ) :
    wt (LL.snoc n) (K + 1) c (FB.ext n ρ m') = wt LL K c m' - (if c = ρ then (n : ℤ) else 0) := by
  unfold wt
  rw [Fin.sum_univ_castSucc]
  simp only [FB.ext_castSucc, FB.ext_last, FB.snoc_vec_castSucc, FB.snoc_vec_last, Fin.val_castSucc, Fin.val_last,
    Nat.lt_succ_self, if_true, Bool.false_eq_true, if_false]
  have e : ∀ i : Fin K, ((i : ℕ) < K + 1) = True := fun i => by simp
  have e' : ∀ i : Fin K, ((i : ℕ) < K) = True := fun i => by simp
  simp only [e, e', if_true]
  split_ifs <;> simp [sub_eq_add_neg]
end Formalism.CountingSumsFrames
