-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.gF_eta_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:07.93413+00:00
-- url     : https://prove2.me/submissions/0a058c29-7a20-4c82-a23a-7b2edddce81f

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_F
import Theorems.Thm_Formalism_GM_leadingTermLemmas_wW_inj
import Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_e__inj_b83b9739b71a
import Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_wW_ne_e__a87a32810661
import Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_biHom_sq__c19e50466e6a
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
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ)
variable (hv : LL.vec (Fin.last N) = true) (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m)
  (hme : e ≤ m (Fin.last N, ρ)) (n : ℕ) (hn : LL.total ≤ n)
include hm hme hn
omit hn
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution : ∀ M ∈ (gF (K := K) LL ρ e m).support, M (Fin.last (N + 1), ρ) ≤ LL.total - e := by
  intro M hM
  unfold gF at hM
  by_cases h : m (Fin.last N, ρ) = e
  · rw [if_pos h] at hM
    have hb := (biHom_F wW_inj eη_inj wW_ne_eη (biHom_sq' (K := K) LL ρ m hm)).1
    have h2 := (hb M hM).2
    have h3 : M (Fin.last (N + 1), ρ) ≤ ∑ c, M (eη (N := N) c) :=
      Finset.single_le_sum (f := fun c => M (eη (N := N) c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ρ)
    simp only [eη] at h2 h3
    omega
  · rw [if_neg h] at hM; simp at hM
end Formalism.GM.leadingTermLemmas
