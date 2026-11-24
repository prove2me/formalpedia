-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.Z_biHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:04.4368+00:00
-- url     : https://prove2.me/submissions/38c544ab-4743-4120-95ed-1745b88debfb

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_weight_ind
import Theorems.Thm_Formalism_GM_GammaExpansion_q_isWH
import Theorems.Thm_Formalism_GM_GammaExpansion_degW_eq
import Theorems.Thm_Formalism_GM_GammaExpansion_degH_eq
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
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ) (he : e ≤ LL.deg (Fin.last N))
    (h : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hh : h ∈ M.Pol p r (lowerLast LL e)) (m0 : ℕ) :
    BiHom (fun c : Fin r => (Fin.castSucc (Fin.last N), c)) (fun c : Fin r => (Fin.last (N + 1), c))
      (LL.deg (Fin.last N) - e) (m0 + (LL.total - e))
      (X (Fin.last (N + 1), ρ) ^ m0 * aeval (M.freezeSub p LL ρ) h) := by
  classical
  intro m hm
  rw [mem_support_iff, X_pow_eq_monomial, coeff_monomial_mul'] at hm
  split_ifs at hm with hle
  · rw [one_mul] at hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single (Fin.last (N + 1), ρ) m0 :=
      ⟨_, (tsub_add_cancel_of_le hle).symm⟩
    rw [add_tsub_cancel_right] at hm
    have hW : Finsupp.weight (fun x : Fin (N + 1 + 1) × Fin r =>
        (if x.1 = Fin.castSucc (Fin.last N) then 1 else 0)) m' = LL.deg (Fin.last N) - e := by
      rw [← degW_eq LL e]
      exact q_isWH p LL ρ e h hh (fun b' => if b' = Fin.castSucc (Fin.last N) then 1 else 0) hm
    have hH : Finsupp.weight (fun x : Fin (N + 1 + 1) × Fin r =>
        (if x.1 = Fin.last (N + 1) then 1 else 0)) m' = LL.total - e := by
      rw [← degH_eq LL e he]
      exact q_isWH p LL ρ e h hh (fun b' => if b' = Fin.last (N + 1) then 1 else 0) hm
    rw [weight_ind] at hW hH
    refine ⟨?_, ?_⟩
    · simp only [Finsupp.add_apply, Finset.sum_add_distrib, hW]
      simp [Finsupp.single_apply, (Fin.castSucc_lt_last (Fin.last N)).ne']
    · simp only [Finsupp.add_apply, Finset.sum_add_distrib, hH]
      simp [Finsupp.single_apply, add_comm]
  · exact absurd rfl hm
end Formalism.GM.GammaExpansion
