-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.quot_mem_pol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:12.5552+00:00
-- url     : https://prove2.me/submissions/dc00b98b-a94c-41f3-90f3-1b1499eb3455

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_congr
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
theorem _root_.solution (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ) (f h : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (hf : f ∈ M.Pol p r LL) (hh : ∀ m ∈ h.support, Finsupp.single (Fin.last N, ρ) e + m ∈ f.support) :
    h ∈ M.Pol p r (lowerLast LL e) := by
  classical
  simp only [M.Pol, MvPolynomial.mem_restrictSupport_iff] at hf ⊢
  intro m hm
  have h1 : M.MultiDeg LL (Finsupp.single (Fin.last N, ρ) e + m) := hf (hh m hm)
  show M.MultiDeg (lowerLast LL e) m
  intro i
  have h2 := h1 i
  have hs : ∑ c, (Finsupp.single (Fin.last N, ρ) e + m : Fin (N + 1) × Fin r →₀ ℕ) (i, c) =
      (if i = Fin.last N then e else 0) + ∑ c, m (i, c) := by
    simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    congr 1
    by_cases hi : i = Fin.last N
    · subst hi
      rw [Finset.sum_eq_single ρ]
      · simp
      · intro c _ hc; simp [Finsupp.single_apply, Ne.symm hc]
      · simp
    · rw [if_neg hi]
      exact Finset.sum_eq_zero fun c _ => by simp [Finsupp.single_apply, Ne.symm hi]
  rw [hs] at h2
  show ∑ c, m (i, c) = Function.update LL.deg (Fin.last N) (LL.deg (Fin.last N) - e) i
  by_cases hi : i = Fin.last N
  · subst hi; simp at h2 ⊢ <;> omega
  · simpa [hi] using h2
end Formalism.GM.GammaExpansion
