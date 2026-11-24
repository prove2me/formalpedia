-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.pderiv_W_fSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:39.600802+00:00
-- url     : https://prove2.me/submissions/05fa32fe-07fc-4678-825a-e5ca1319656a

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
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
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (hv : LL.vec (Fin.last N) = true) (x : Fin (N + 1) × Fin r) (hx : x ≠ (Fin.last N, ρ)) :
    pderiv (wW (N := N) ρ) (fSub K LL ρ x) = 0 := by
  obtain ⟨i, c⟩ := x
  have hXcs : ∀ c', (i = Fin.last N → c' ≠ ρ) →
      pderiv (wW (N := N) ρ) (X (Fin.castSucc i, c') : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) = 0 := by
    intro c' hc'
    apply pderiv_X_of_ne
    intro h
    simp only [wW, Prod.mk.injEq, Fin.castSucc_inj] at h
    exact hc' h.1 h.2
  have hXe : ∀ c', pderiv (wW (N := N) ρ) (X (Fin.last (N + 1), c') : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) = 0 := by
    intro c'; apply pderiv_X_of_ne
    intro h; simp only [wW, Prod.mk.injEq] at h; exact Fin.castSucc_ne_last _ h.1.symm
  simp only [fSub]
  by_cases hvi : LL.vec i = true <;> by_cases hc : c = ρ
  · rw [if_pos hvi, if_pos hc]
    have hi : i ≠ Fin.last N := fun h => hx (by rw [h, hc])
    rw [map_sum]; refine Finset.sum_eq_zero (fun c' _ => ?_)
    rw [Derivation.leibniz, hXcs c' (fun h => absurd h hi), hXe]; simp
  · rw [if_pos hvi, if_neg hc, Derivation.leibniz, hXcs c (fun _ => hc), hXe]; simp
  · have hi : i ≠ Fin.last N := fun h => hvi (h ▸ hv)
    rw [if_neg hvi, if_pos hc, Derivation.leibniz, hXcs ρ (fun h => absurd h hi), hXe]; simp
  · have hi : i ≠ Fin.last N := fun h => hvi (h ▸ hv)
    rw [if_neg hvi, if_neg hc, map_sub, Derivation.leibniz, Derivation.leibniz, hXcs c (fun h => absurd h hi),
      hXcs ρ (fun h => absurd h hi), hXe, hXe]; simp
end Formalism.GM.leadingTermLemmas
