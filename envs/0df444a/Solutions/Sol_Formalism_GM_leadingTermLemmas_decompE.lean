-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.decompE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:21.089576+00:00
-- url     : https://prove2.me/submissions/d45547c1-b4ce-437f-832b-7df9ac8799e4

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_zero
import Theorems.Thm_Formalism_GM_leadingTermLemmas_decomp
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
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
  (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution {K : Type} [Field K] [CharZero K] (hr : 1 ≤ r) (A B : ℕ) (y : MvPolynomial σ K)
    (hy : BiHom w e (A - 1) (B - 1) y) (hy0 : y ≠ 0 → 1 ≤ A ∧ 1 ≤ B) :
    ∃ yl : ℕ → MvPolynomial σ K, tieE w e y = ∑ l ∈ range A, (tieE w e ^ (l + 1)) (yl l) ∧
      ∀ l ∈ range A, tieF w e (yl l) = 0 ∧ BiHom w e (A - 1 - l) (B - 1 - l) (yl l) := by
  by_cases h : y = 0
  · refine ⟨fun _ => 0, by simp [h], fun l _ => ⟨map_zero _, biHom_zero _ _⟩⟩
  · obtain ⟨hA, hB⟩ := hy0 h
    obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hy ⊢
    obtain ⟨yl, hyl, hc⟩ := decomp hw he hwe hr A' (B - 1) y hy
    refine ⟨yl, ?_, fun l hl => ⟨(hc l hl).1, (hc l hl).2.1⟩⟩
    rw [hyl, map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [pow_succ', Module.End.mul_apply]
end Formalism.GM.leadingTermLemmas
