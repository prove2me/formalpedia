-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.limit_value
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:58.837505+00:00
-- url     : https://prove2.me/submissions/2beaa03f-51e8-4ceb-b41c-2bc9740dd851

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_zero_left
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_zero_right
import Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_biHom_sq__c19e50466e6a
import Theorems.Thm_Formalism_GM_leadingTermLemmas_top_eq_kill
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_monomial
import Theorems.Thm_Formalism_GM_leadingTermLemmas_wf_split
import Theorems.Thm_Formalism_GM_leadingTermLemmas_update_eq_iff
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_kill_sq
import Theorems.Thm_Formalism_GM_leadingTermLemmas_sum_update_eq
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
open MvPolynomial Finset Formalism.GM Filter Topology
variable {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (z e : ℕ) (m m' : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) (hm' : M.MultiDeg LL m') :
    (1 / ((LL.deg (Fin.last N)).factorial : ℝ)) *
      (((z + e).choose e : ℝ) * e.factorial * e.factorial *
        (if m (Fin.last N, ρ) = e ∧ m' (Fin.last N, ρ) = e then
          ∑ M ∈ (sq (K := ℝ) LL ρ m).support, (sq LL ρ m).coeff M * (sq LL ρ m').coeff M * wf M *
            (if M (Fin.last (N + 1), ρ) = LL.total - e then 1 / ((LL.total - e).factorial : ℝ) else 0)
        else 0) + 0) /
      (((LL.total).factorial : ℝ) * ∏ i, ((LL.deg i).factorial : ℝ)) =
    (((e.factorial * (z + e).choose e : ℕ) : ℝ) * fk (inMono (K := ℝ) ρ e m) (inMono ρ e m')) /
      ((((LL.deg (Fin.last N)).factorial * LL.total.factorial : ℕ) : ℝ) * ∏ i, ((LL.deg i).factorial : ℝ)) := by
  have ho : ((LL.deg (Fin.last N)).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hS : ((LL.total).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hd : ((LL.total - e).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hpr : (∏ i, ((LL.deg i).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.factorial_ne_zero _)
  by_cases h : m (Fin.last N, ρ) = e ∧ m' (Fin.last N, ρ) = e
  · rw [if_pos h]
    have hT : ∑ M ∈ (sq (K := ℝ) LL ρ m).support, (sq LL ρ m).coeff M * (sq LL ρ m').coeff M * wf M *
        (if M (Fin.last (N + 1), ρ) = LL.total - e then 1 / ((LL.total - e).factorial : ℝ) else 0) =
        fk (kill (K := ℝ) (Pη ρ) (sq LL ρ m)) (kill (Pη ρ) (sq LL ρ m')) / ((LL.total - e).factorial : ℝ) := by
      have hb := biHom_sq' (K := ℝ) LL ρ m hm
      rw [h.1] at hb
      rw [← top_eq_kill ρ _ _ _ _ hb, Finset.sum_div]
      refine Finset.sum_congr rfl (fun M _ => ?_)
      split_ifs <;> ring
    rw [hT, fk_kill_sq LL ρ m m' (LL.total - e) (by rw [sum_update_eq LL ρ m hm, h.1])
      (by rw [sum_update_eq LL ρ m' hm', h.2])]
    unfold inMono
    rw [if_pos h.1, if_pos h.2, fk_monomial, wf_split ρ m, h.1]
    by_cases hq : Finsupp.update m (Fin.last N, ρ) 0 = Finsupp.update m' (Fin.last N, ρ) 0
    · rw [if_pos hq, if_pos ((update_eq_iff ρ m m' (h.1.trans h.2.symm)).mp hq)]
      push_cast
      field_simp
      ring
    · rw [if_neg hq, if_neg (fun h' => hq ((update_eq_iff ρ m m' (h.1.trans h.2.symm)).mpr h'))]
      simp
  · rw [if_neg h]
    have : fk (inMono (K := ℝ) ρ e m) (inMono ρ e m') = 0 := by
      unfold inMono
      by_cases h1 : m (Fin.last N, ρ) = e
      · rw [if_neg (fun h2 => h ⟨h1, h2⟩), fk_zero_right]
      · rw [if_neg h1, fk_zero_left]
    rw [this]; simp
end Formalism.GM.leadingTermLemmas
