-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.IsPD.choose_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:07.813306+00:00
-- url     : https://prove2.me/submissions/ca166b77-50dd-46d3-a46c-6f703f2f1464

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_choose_sub
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
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open Polynomial Finset
variable {k : Type} [Field k] [CharZero k]
namespace Formalism.GM.GammaExpansion
namespace IsPD
theorem _root_.solution (S i t : ℕ) :
    IsPD S (i + t) (fun n => ((((n - S).choose i * (n - S - i).choose t : ℕ)) : k)) := by
  obtain ⟨P1, hd1, h1⟩ := IsPD.choose_sub (k := k) S i
  obtain ⟨P2, hd2, h2⟩ := IsPD.choose_sub (k := k) (S + i) t
  have h1' : ∀ n, S ≤ n → ((((n - S).choose i : ℕ)) : k) = P1.eval (n : k) := h1
  have h2' : ∀ n, S + i ≤ n → ((((n - S - i).choose t : ℕ)) : k) = P2.eval (n : k) := by
    intro n hn; rw [Nat.sub_sub]; exact h2 n hn
  refine ⟨P1 * P2, Polynomial.natDegree_mul_le.trans (add_le_add hd1 hd2), fun n hn => ?_⟩
  show ((((n - S).choose i * (n - S - i).choose t : ℕ)) : k) = _
  rw [Polynomial.eval_mul, ← h1' n hn]
  by_cases h : S + i ≤ n
  · rw [← h2' n h, Nat.cast_mul]
  · have h0 : (n - S).choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0]
end IsPD
end Formalism.GM.GammaExpansion
