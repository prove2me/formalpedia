-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.main_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:04.445205+00:00
-- url     : https://prove2.me/submissions/647aa3cd-6712-4887-9d93-6706ab7c42e6

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_tieE_pow_apply
import Theorems.Thm_Formalism_GM_GammaExpansion_pow_Dp_omega_mul
import Theorems.Thm_Formalism_GM_GammaExpansion_pow_Dp_X_pow_mul
import Theorems.Thm_Formalism_GM_GammaExpansion_powDp_comm_powF
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
theorem _root_.solution (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (ρ : Fin r) (q : MvPolynomial σ k)
    (K : ℕ) (hq : ∀ s ∈ q.support, s (e ρ) ≤ K) (s j m : ℕ) :
    (Dp (e ρ) ^ m) ((tieE w e ^ s) ((tieF w e ^ j) (X (e ρ) ^ m * q))) =
      (m.factorial : k) • ∑ i ∈ range (s + 1), ∑ t ∈ range (K + 1),
        (((m.choose i * (m - i).choose t : ℕ) : k) * (s.descFactorial i : k) / ((i + t).factorial : k)) •
          (X (w ρ) ^ i * (∑ c, X (w c) * X (e c)) ^ (s - i) *
            (tieF w e ^ j) (X (e ρ) ^ (i + t) * (Dp (e ρ) ^ t) q)) := by
  rw [tieE_pow_apply, pow_Dp_omega_mul he hwe ρ s m, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [powDp_comm_powF, mul_comm (X (e ρ) ^ m) q, pow_Dp_X_pow_mul (e ρ) q K (m - i) m hq, map_sum,
    Finset.mul_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [map_nsmul, mul_smul_comm, smul_smul]
  rw [← Nat.cast_smul_eq_nsmul k]
  by_cases him : i ≤ m
  · by_cases hit : t ≤ m - i
    · have he1 : m - (m - i - t) = i + t := by omega
      rw [he1, mul_comm ((Dp (e ρ) ^ t) q)]
      congr 1
      have hf := Nat.factorial_mul_descFactorial (show m - i - t ≤ m by omega)
      rw [he1] at hf
      have hne : ((i + t).factorial : k) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      rw [← hf]
      push_cast
      first
      | (field_simp; ring)
      | field_simp
    · have h0 : (m - i).choose t = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h0]
  · have h0 : m.choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0]
end Formalism.GM.GammaExpansion
