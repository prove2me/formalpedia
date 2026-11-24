-- Prove2me | solution 1 for Formalism.GM.gamma_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:02.937057+00:00
-- url     : https://prove2.me/submissions/c56ea9b7-3172-410a-82f9-a59a130ea9e9

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_phi_symm
import Theorems.Thm_Formalism_GM_GammaExpansion_gam_oneSided
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
open Formalism Formalism.GM
open MvPolynomial Finset
namespace Formalism.GM
theorem _root_.solution : M.GamDeg := by
  intro p _ N r LL ρ z e e' f f' hr hvec hf hf' ho ho'
  have hsym : ∀ n, M.tieGam p LL ρ z n f f' = M.tieGam p LL ρ z n f' f := by
    intro n
    simp only [M.tieGam, M.tiePhiAt]
    rw [GammaExpansion.fock_phi_symm]
  have hle : ∀ (g : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (d : ℕ), g ∈ M.Pol p r LL →
      M.HasOrder (Fin.last N, ρ) d g → d ≤ LL.deg (Fin.last N) := by
    intro g d hg hgo
    obtain ⟨_, m, hm, hmd⟩ := hgo
    simp only [M.Pol, MvPolynomial.mem_restrictSupport_iff] at hg
    have h2 : ∑ c, m (Fin.last N, c) = LL.deg (Fin.last N) := hg hm (Fin.last N)
    rw [← hmd, ← h2]
    exact Finset.single_le_sum (f := fun c => m (Fin.last N, c)) (fun c _ => Nat.zero_le _) (Finset.mem_univ ρ)
  rcases le_total e' e with h | h
  · obtain ⟨P, hP, hP'⟩ := GammaExpansion.gam_oneSided p N r LL ρ z e f f' hr hvec hf ho.1 (hle f e hf ho)
    exact ⟨P, by rw [max_eq_left h]; exact hP, hP'⟩
  · obtain ⟨P, hP, hP'⟩ := GammaExpansion.gam_oneSided p N r LL ρ z e' f' f hr hvec hf' ho'.1 (hle f' e' hf' ho')
    exact ⟨P, by rw [max_eq_right h]; exact hP, fun n hn => (hsym n).trans (hP' n hn)⟩
end Formalism.GM
