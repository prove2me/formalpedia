-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.pow_Dp_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:34.407154+00:00
-- url     : https://prove2.me/submissions/08caea97-5bdf-4cd4-b9ca-b45678668d4f

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_pow_Dp_mul
import Theorems.Thm_Formalism_GM_GammaExpansion_pow_Dp_X_pow
import Theorems.Thm_Formalism_GM_GammaExpansion_pow_Dp_eq_zero
import Theorems.Thm_Formalism_GM_GammaExpansion_sum_range_eq_of_zero
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
theorem _root_.solution (v : σ) (q : MvPolynomial σ k) (K M m : ℕ) (hq : ∀ s ∈ q.support, s v ≤ K) :
    (Dp v ^ M) (q * X v ^ m) =
      ∑ i ∈ range (K + 1), (M.choose i * m.descFactorial (M - i)) • ((Dp v ^ i) q * X v ^ (m - (M - i))) := by
  have hz : ∀ i, K + 1 ≤ i → (Dp v ^ i) q = 0 := by
    intro i hi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [show K + 1 + d = d + (K + 1) by ring, pow_add]
    show (Dp v ^ d) ((Dp v ^ (K + 1)) q) = 0
    rw [pow_Dp_eq_zero v q K hq, map_zero]
  rw [pow_Dp_mul]
  have hfe : ∀ i, M.choose i • ((Dp v ^ i) q * (Dp v ^ (M - i)) (X v ^ m)) =
      (M.choose i * m.descFactorial (M - i)) • ((Dp v ^ i) q * X v ^ (m - (M - i))) := by
    intro i
    rw [pow_Dp_X_pow, mul_smul_comm, smul_smul]
  simp only [hfe]
  exact sum_range_eq_of_zero _ (M + 1) (K + 1)
    (fun i hi => by simp [Nat.choose_eq_zero_of_lt (show M < i by omega)])
    (fun i hi => by simp [hz i hi])
end Formalism.GM.GammaExpansion
