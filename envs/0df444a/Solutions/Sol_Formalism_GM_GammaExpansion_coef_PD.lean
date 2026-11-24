-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.coef_PD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:34.384609+00:00
-- url     : https://prove2.me/submissions/cbc7385d-40ae-4560-b971-8aa321e06007

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_const
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_congr
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_mul
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_choose_add
import Theorems.Thm_Formalism_GM_GammaExpansion_coef_nat
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
open Finset
variable {k : Type} [Field k] [CharZero k]
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (o r z s j S : ℕ) (hr : 1 ≤ r) (hsj : s + j ≤ o) (hoS : o ≤ S) :
    IsPD S (o - s - j) (fun n => (((o + n + r + z - 1).choose o : ℕ) : k) *
      (∏ i ∈ range s, (((z : k) + 1 + i) / ((o + n + r + z - 1 - i : ℕ) : k))) *
        cph k ((o - s) + (n - s) + r + (z + s) - 1) j) := by
  have hK := (IsPD.choose_add (k := k) S (o + r + z - 1 - s - j) (o - s - j)).mul
    (IsPD.const S 0 (((o - s - j).factorial : k) * (∏ i ∈ range s, ((z : k) + 1 + i)) * (-1) ^ j /
      ((o.factorial : k) * (j.factorial : k))))
  rw [add_zero] at hK
  refine hK.congr fun n hn => ?_
  beta_reduce
  have hA : (o - s) + (n - s) + r + (z + s) - 1 = o + n + r + z - 1 - s := by omega
  have hc : o + n + r + z - 1 - s - j = n + (o + r + z - 1 - s - j) := by omega
  have hnat := coef_nat (o + n + r + z - 1) o s j hsj
  rw [hc] at hnat
  have hprod : ∏ i ∈ range s, (((z : k) + 1 + i) / ((o + n + r + z - 1 - i : ℕ) : k)) =
      (∏ i ∈ range s, ((z : k) + 1 + i)) / (((o + n + r + z - 1).descFactorial s : ℕ) : k) := by
    rw [Finset.prod_div_distrib, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  rw [hA, hprod]
  have ho : (o.factorial : k) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero o
  have hj : (j.factorial : k) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hCj : (((o + n + r + z - 1 - s).choose j : ℕ) : k) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hD : (((o + n + r + z - 1).descFactorial s : ℕ) : k) ≠ 0 := by
    have : (o + n + r + z - 1).descFactorial s ≠ 0 := fun h0 => by
      rw [Nat.descFactorial_eq_zero_iff_lt] at h0; omega
    exact_mod_cast this
  have hk := congrArg (Nat.cast : ℕ → k) hnat
  push_cast at hk
  have hX : (((o + n + r + z - 1).choose o : ℕ) : k) =
      ((n + (o + r + z - 1 - s - j)).choose (o - s - j) : k) * ((o - s - j).factorial : k) *
        (((o + n + r + z - 1 - s).choose j : k) * (j.factorial : k)) *
        ((o + n + r + z - 1).descFactorial s : k) / (o.factorial : k) := by
    rw [eq_div_iff ho]; exact hk
  rw [hX]
  simp only [cph]
  first
  | (field_simp; ring)
  | field_simp
end Formalism.GM.GammaExpansion
