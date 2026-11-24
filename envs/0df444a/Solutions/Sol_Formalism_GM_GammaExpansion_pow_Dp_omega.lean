-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.pow_Dp_omega
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:53.563487+00:00
-- url     : https://prove2.me/submissions/eac164e6-9a24-4eb9-b61a-03e9c78f28f0

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_Dp_apply
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
theorem _root_.solution (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (ρ : Fin r) (s i : ℕ) :
    (Dp (e ρ) ^ i) ((∑ c, X (w c) * X (e c)) ^ s : MvPolynomial σ k) =
      s.descFactorial i • (X (w ρ) ^ i * (∑ c, X (w c) * X (e c)) ^ (s - i)) := by
  classical
  have hD : pderiv (e ρ) (∑ c, X (w c) * X (e c) : MvPolynomial σ k) = X (w ρ) := by
    simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, he.eq_iff, hwe]
  have hX : pderiv (e ρ) (X (w ρ) : MvPolynomial σ k) = 0 := by
    rw [pderiv_X, Pi.single_apply, if_neg (hwe ρ ρ)]
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ']
    show Dp (e ρ) ((Dp (e ρ) ^ i) _) = _
    rw [ih, map_nsmul, Dp_apply]
    simp only [Derivation.leibniz, Derivation.leibniz_pow, hD, hX, smul_zero, add_zero, smul_eq_mul, nsmul_eq_mul,
      Nat.descFactorial_succ, Nat.cast_mul, Nat.sub_sub, mul_zero]
    ring
end Formalism.GM.GammaExpansion
