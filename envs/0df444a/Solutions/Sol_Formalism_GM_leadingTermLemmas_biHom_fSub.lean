-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.biHom_fSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:05.648804+00:00
-- url     : https://prove2.me/submissions/cc042ec0-32ba-4cea-89c7-973e5868406b

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_sub
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_sum
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_mul
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_Xcs
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_Xeta
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
theorem _root_.solution (x : Fin (N + 1) × Fin r) :
    BiHom (wW (N := N)) eη (if x.1 = Fin.last N then 1 else 0) 1 (fSub K LL ρ x) := by
  obtain ⟨i, c⟩ := x
  have hp : ∀ c1 c2, BiHom (wW (N := N)) eη (if i = Fin.last N then 1 else 0) 1
      ((X (Fin.last (N + 1), c1) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) * X (Fin.castSucc i, c2)) := by
    intro c1 c2
    have := biHom_mul (biHom_Xeta (K := K) (N := N) c1) (biHom_Xcs (K := K) i c2)
    simpa [add_comm] using this
  have hp' : ∀ c1 c2, BiHom (wW (N := N)) eη (if i = Fin.last N then 1 else 0) 1
      ((X (Fin.castSucc i, c2) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) * X (Fin.last (N + 1), c1)) := by
    intro c1 c2; rw [mul_comm]; exact hp c1 c2
  simp only [fSub]
  by_cases hv : LL.vec i = true <;> by_cases hc : c = ρ
  · rw [if_pos hv, if_pos hc]; exact biHom_sum _ _ (fun c' _ => hp' c' c')
  · rw [if_pos hv, if_neg hc]; exact hp ρ c
  · rw [if_neg hv, if_pos hc]; exact hp ρ ρ
  · rw [if_neg hv, if_neg hc]; exact biHom_sub (hp ρ c) (hp' c ρ)
end Formalism.GM.leadingTermLemmas
