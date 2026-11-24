-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_kill_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:23.517028+00:00
-- url     : https://prove2.me/submissions/b2453acf-b847-43cb-924b-1759c9685ad4

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_Xpow
import Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_cs__inj_ca937efcfb8b
import Theorems.Thm_Formalism_GM_leadingTermLemmas_kill_sq
import Theorems.Thm_Formalism_GM_leadingTermLemmas_wf_mapDomain
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
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (m m' : Fin (N + 1) × Fin r →₀ ℕ) (d : ℕ)
    (hd : ∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x = d) (hd' : ∑ x, (Finsupp.update m' (Fin.last N, ρ) 0) x = d) :
    fk (kill (K := K) (Pη ρ) (sq LL ρ m)) (kill (Pη ρ) (sq LL ρ m')) =
      if Finsupp.update m (Fin.last N, ρ) 0 = Finsupp.update m' (Fin.last N, ρ) 0 then
        (d.factorial : K) * wf (Finsupp.update m (Fin.last N, ρ) 0) else 0 := by
  classical
  rw [kill_sq, kill_sq, hd, hd', fk_Xpow, support_monomial, if_neg one_ne_zero, Finset.sum_singleton,
    coeff_monomial, if_pos rfl, coeff_monomial, wf_mapDomain]
  have h0 : ((Finsupp.update m (Fin.last N, ρ) 0).mapDomain (cs' (N := N))) (Fin.last (N + 1), ρ) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨x, hx⟩
    simp only [cs', Prod.mk.injEq] at hx
    exact Fin.castSucc_ne_last _ hx.1
  rw [h0, zero_add, Nat.descFactorial_self]
  by_cases h : Finsupp.update m (Fin.last N, ρ) 0 = Finsupp.update m' (Fin.last N, ρ) 0
  · rw [h]; simp; ring
  · have h'' : ¬ ((Finsupp.update m' (Fin.last N, ρ) 0).mapDomain (cs' (N := N)) =
        (Finsupp.update m (Fin.last N, ρ) 0).mapDomain (cs' (N := N))) :=
      fun h' => h (Finsupp.mapDomain_injective cs'_inj h').symm
    rw [if_neg h'', if_neg h]; ring
end Formalism.GM.leadingTermLemmas
