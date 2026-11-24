-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.pow_Dp_omega_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:10.736033+00:00
-- url     : https://prove2.me/submissions/03157e09-7835-410a-8806-670958e63a0c

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_pow_Dp_mul
import Theorems.Thm_Formalism_GM_GammaExpansion_sum_range_eq_of_zero
import Theorems.Thm_Formalism_GM_GammaExpansion_pow_Dp_omega
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
theorem _root_.solution (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (ρ : Fin r) (s m : ℕ)
    (V : MvPolynomial σ k) :
    (Dp (e ρ) ^ m) ((∑ c, X (w c) * X (e c)) ^ s * V) =
      ∑ i ∈ range (s + 1), (m.choose i * s.descFactorial i) •
        (X (w ρ) ^ i * (∑ c, X (w c) * X (e c)) ^ (s - i) * (Dp (e ρ) ^ (m - i)) V) := by
  rw [pow_Dp_mul]
  have hfe : ∀ i, m.choose i • ((Dp (e ρ) ^ i) ((∑ c, X (w c) * X (e c)) ^ s) * (Dp (e ρ) ^ (m - i)) V) =
      (m.choose i * s.descFactorial i) •
        (X (w ρ) ^ i * (∑ c, X (w c) * X (e c)) ^ (s - i) * (Dp (e ρ) ^ (m - i)) V) := by
    intro i
    rw [pow_Dp_omega he hwe, smul_mul_assoc, smul_smul]
  simp only [hfe]
  exact sum_range_eq_of_zero _ (m + 1) (s + 1)
    (fun i hi => by simp [Nat.choose_eq_zero_of_lt (show m < i by omega)])
    (fun i hi => by simp [Nat.descFactorial_eq_zero_iff_lt.2 (show s < i by omega)])
end Formalism.GM.GammaExpansion
