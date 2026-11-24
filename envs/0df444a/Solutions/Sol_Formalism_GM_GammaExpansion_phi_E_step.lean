-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.phi_E_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:26.28086+00:00
-- url     : https://prove2.me/submissions/98e0f92a-d88d-417a-9cc6-ac34f15b3fe8

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_EW_Fpow
import Theorems.Thm_Formalism_GM_GammaExpansion_Fpow_E
import Theorems.Thm_Formalism_GM_GammaExpansion_eq_zero_of_EW
import Theorems.Thm_Formalism_GM_GammaExpansion_cph_step
import Theorems.Thm_Formalism_GM_GammaExpansion_tiePhi_eq
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
theorem _root_.solution (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (o' n' z : ℕ) (Z : MvPolynomial σ k) (hW : EW w Z = (o' : k) • Z) (hE : EW e Z = (n' : k) • Z) :
    tiePhi w e (o' + 1) (n' + 1) z (tieE w e Z) =
      (((z : k) + 1) / ((o' + n' + r + z + 1 : ℕ) : k)) • tieE w e (tiePhi w e o' n' (z + 1) Z) := by
  have hE2 : ∀ (t : ℕ) (x : MvPolynomial σ k), tieE w e ((tieE w e ^ t) x) = (tieE w e ^ (t + 1)) x := by
    intro t x; rw [pow_succ'] <;> rfl
  have hE1 : ∀ (t : ℕ) (x : MvPolynomial σ k), (tieE w e ^ t) (tieE w e x) = (tieE w e ^ (t + 1)) x := by
    intro t x; rw [pow_succ] <;> rfl
  have hvan : (tieF w e ^ (o' + 1)) Z = 0 :=
    eq_zero_of_EW (w := w) o' (o' + 1) (by omega) _ (EW_Fpow hw hwe (o' : k) Z hW (o' + 1))
  have hG : ∀ t : ℕ, (tieE w e ^ (t + 1)) ((tieF w e ^ (t + 1)) (tieE w e Z)) =
      (tieE w e ^ (t + 1 + 1)) ((tieF w e ^ (t + 1)) Z) +
        (((t : k) + 1) * ((o' : k) + n' + r - t)) • (tieE w e ^ (t + 1)) ((tieF w e ^ t) Z) := by
    intro t
    rw [Fpow_E hw he hwe (o' : k) (n' : k) Z hW hE t, map_add, map_smul, hE1]
  have hA1 : o' + 1 + (n' + 1) + r + z - 1 = o' + n' + r + z + 1 := by omega
  have hA2 : o' + n' + r + (z + 1) - 1 = o' + n' + r + z := by omega
  rw [tiePhi_eq, tiePhi_eq, hA1, hA2, map_sum, Finset.smul_sum]
  conv_lhs => rw [Finset.sum_range_succ']
  beta_reduce
  simp only [hG, smul_add, smul_smul, Finset.sum_add_distrib, map_smul, hE2]
  have h0 : (tieE w e ^ 0) ((tieF w e ^ 0) (tieE w e Z)) = (tieE w e ^ (0 + 1)) ((tieF w e ^ 0) Z) := by simp
  rw [h0]
  have hs2 := Finset.sum_range_succ'
    (fun t => cph k (o' + n' + r + z + 1) t • (tieE w e ^ (t + 1)) ((tieF w e ^ t) Z)) (o' + 1)
  rw [Finset.sum_range_succ (fun t => cph k (o' + n' + r + z + 1) t • (tieE w e ^ (t + 1)) ((tieF w e ^ t) Z))
    (o' + 1)] at hs2
  beta_reduce at hs2
  rw [hvan, map_zero, smul_zero, add_zero] at hs2
  rw [add_right_comm, ← hs2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [← add_smul, cph_step (o' + n' + r + z) t o' n' z rfl (by have := Finset.mem_range.1 ht; omega)]
end Formalism.GM.GammaExpansion
