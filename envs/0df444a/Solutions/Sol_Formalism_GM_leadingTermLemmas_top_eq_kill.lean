-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.top_eq_kill
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:58.33624+00:00
-- url     : https://prove2.me/submissions/1878206a-e697-4c37-936a-4d308f05d916

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_eq_sum
import Theorems.Thm_Formalism_GM_leadingTermLemmas_coeff_kill
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
theorem _root_.solution (a d : ℕ) (g g' : MvPolynomial (Fin (N + 1 + 1) × Fin r) K)
    (hg : BiHom (wW (N := N)) eη a d g) :
    ∑ M ∈ g.support, g.coeff M * g'.coeff M * wf M * (if M (Fin.last (N + 1), ρ) = d then 1 else 0) =
      fk (kill (Pη ρ) g) (kill (Pη ρ) g') := by
  have hs : (kill (K := K) (Pη ρ) g).support ⊆ g.support := by
    intro M hM
    rw [mem_support_iff, coeff_kill] at hM
    split_ifs at hM
    · exact mem_support_iff.mpr hM
    · exact absurd rfl hM
  rw [fk_eq_sum _ _ _ hs]
  refine Finset.sum_congr rfl (fun M hM => ?_)
  rw [coeff_kill, coeff_kill]
  have hd := (hg M hM).2
  have key : (∀ v, Pη (N := N) ρ v → M v = 0) ↔ M (Fin.last (N + 1), ρ) = d := by
    rw [← hd, ← Finset.add_sum_erase _ _ (Finset.mem_univ ρ)]
    constructor
    · intro h
      rw [Finset.sum_eq_zero (fun c hc => h _ ⟨rfl, Finset.ne_of_mem_erase hc⟩), add_zero]
    · intro h v hv
      obtain ⟨v1, v2⟩ := v
      simp only [Pη] at hv
      obtain ⟨rfl, hv2⟩ := hv
      have h0 : ∑ c ∈ Finset.univ.erase ρ, M (eη (N := N) c) = 0 := by simp only [eη] at h ⊢; omega
      exact (Finset.sum_eq_zero_iff.mp h0) v2 (Finset.mem_erase.mpr ⟨hv2, Finset.mem_univ _⟩)
  by_cases h : M (Fin.last (N + 1), ρ) = d
  · rw [if_pos (key.mpr h), if_pos (key.mpr h), if_pos h]; ring
  · rw [if_neg (fun h' => h (key.mp h')), if_neg h]; ring
end Formalism.GM.leadingTermLemmas
