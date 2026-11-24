-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.cph_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:51.64681+00:00
-- url     : https://prove2.me/submissions/48ef8fce-3f36-48ca-a2d0-cf3f5c14667d

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
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
open MvPolynomial Finset
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (B t o' n' z : ℕ) (hB : B = o' + n' + r + z) (ht : t ≤ o') :
    cph k (B + 1) t + cph k (B + 1) (t + 1) * (((t : k) + 1) * ((o' : k) + n' + r - t)) =
      ((z : k) + 1) / ((B + 1 : ℕ) : k) * cph k B t := by
  have htB : t ≤ B := by omega
  have hc : ((B.choose t : ℕ) : k) ≠ 0 := by exact_mod_cast (Nat.choose_pos htB).ne'
  have ht1 : (t : k) + 1 ≠ 0 := Nat.cast_add_one_ne_zero t
  have hB1 : (B : k) + 1 ≠ 0 := Nat.cast_add_one_ne_zero B
  have hf : (t.factorial : k) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  have hne : (B : k) + 1 - t ≠ 0 := by
    rw [← Nat.cast_add_one, ← Nat.cast_sub (by omega : t ≤ B + 1)]
    exact_mod_cast (by omega : B + 1 - t ≠ 0)
  have hd : (((B + 1).choose (t + 1) : ℕ) : k) = ((B : k) + 1) * (B.choose t : k) / ((t : k) + 1) := by
    rw [eq_div_iff ht1]
    have h := Nat.add_one_mul_choose_eq B t
    exact_mod_cast h.symm
  have he : (((B + 1).choose t : ℕ) : k) = ((B : k) + 1) * (B.choose t : k) / ((B : k) + 1 - t) := by
    rw [eq_div_iff hne, ← Nat.cast_add_one, ← Nat.cast_sub (by omega : t ≤ B + 1)]
    have h := Nat.choose_mul_succ_eq B t
    exact_mod_cast (by rw [← h, mul_comm] : (B + 1).choose t * (B + 1 - t) = (B + 1) * B.choose t)
  have hB' : (o' : k) + n' + r = (B : k) - z := by rw [hB]; push_cast; ring
  simp only [cph, hd, he, hB', Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring
end Formalism.GM.GammaExpansion
