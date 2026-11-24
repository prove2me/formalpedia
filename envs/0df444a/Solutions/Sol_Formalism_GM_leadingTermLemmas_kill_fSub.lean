-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.kill_fSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:41.968886+00:00
-- url     : https://prove2.me/submissions/909ef9ab-2ddb-4ab2-839b-02a52def07e9

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_kill_X
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
    kill (K := K) (Pη ρ) (fSub K LL ρ x) = X (Fin.last (N + 1), ρ) * X (cs' x) := by
  obtain ⟨i, c⟩ := x
  have hcs : ∀ c', ¬ Pη (N := N) ρ (Fin.castSucc i, c') := fun c' h => Fin.castSucc_ne_last _ h.1
  have he : ∀ c', Pη (N := N) ρ (Fin.last (N + 1), c') ↔ c' ≠ ρ := fun c' => by simp [Pη]
  simp only [fSub, cs']
  by_cases hvi : LL.vec i = true <;> by_cases hc : c = ρ
  · rw [if_pos hvi, if_pos hc, map_sum]
    simp only [map_mul, kill_X, hcs, if_false, he, ite_not]
    rw [Finset.sum_eq_single ρ]
    · subst hc; simp [mul_comm]
    · intro b _ hb; simp [hb]
    · simp
  · rw [if_pos hvi, if_neg hc]; simp only [map_mul, kill_X, hcs, he, if_false]; simp
  · rw [if_neg hvi, if_pos hc]; simp only [map_mul, kill_X, hcs, he, if_false]; subst hc; simp
  · rw [if_neg hvi, if_neg hc]; simp only [map_sub, map_mul, kill_X, hcs, he, if_false]; simp [hc]
end Formalism.GM.leadingTermLemmas
