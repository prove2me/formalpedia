-- Prove2me | solution 1 for Formalism.GM.extendBijOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:44:47.630139+00:00
-- url     : https://prove2.me/submissions/2f5efbd4-ab74-41dc-b77a-5073b426833a

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ev_freeze
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_coeff_ev
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_weight_wL
import Theorems.Thm_Formalism_GM_M_FB_hom_freeze
import Theorems.Thm_Formalism_GM_M_FB_freeze_inv
import Theorems.Thm_Formalism_GM_M_FB_vanish
import Theorems.Thm_Formalism_GM_M_FB_eq_ext_res
import Theorems.Thm_Formalism_GM_M_FB_mem_IntPol_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSimpArgs false
set_option linter.unusedSimpArgs false
open Formalism Formalism.GM
open MvPolynomial Finset M.FB
namespace Formalism.GM
theorem _root_.solution : M.FreezeBij := by
  intro p _ N r LL ρ n hS
  refine ⟨fun f _ g _ h => ?_, fun F hF hinv => ?_⟩
  · calc f = ev p ρ (M.freeze p LL ρ n f) := (ev_freeze LL ρ n f).symm
      _ = ev p ρ (M.freeze p LL ρ n g) := by rw [h]
      _ = g := ev_freeze LL ρ n g
  · obtain ⟨hFpol, hFint⟩ := Submodule.mem_inf.1 hF
    have hFsupp := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 hFpol
    have hFn : ∀ m ∈ F.support, ∑ c, m (Fin.last N, c) = n := fun m hm => by
      have := (hFsupp (Finset.mem_coe.2 hm)) (Fin.last N)
      rwa [snoc_deg_last] at this
    obtain ⟨f, hf⟩ : ∃ f, f = ev p ρ F := ⟨_, rfl⟩
    have hcf : ∀ m', coeff m' f = coeff (ext n ρ m') F := fun m' => by rw [hf]; exact coeff_ev ρ n F hFn m'
    have hfpol : f ∈ M.Pol p r LL := by
      rw [M.Pol, MvPolynomial.mem_restrictSupport_iff]
      intro m' hm'
      have hne : coeff (ext n ρ m') F ≠ 0 := by
        rw [← hcf]
        exact MvPolynomial.mem_support_iff.1 hm'
      have hmd := hFsupp (Finset.mem_coe.2 (MvPolynomial.mem_support_iff.2 hne))
      intro i
      have := hmd (Fin.castSucc i)
      simpa [snoc_deg_castSucc, ext_castSucc] using this
    have hfint : f ∈ M.IntPol p (Fin N × Fin r) := by
      rw [mem_IntPol_iff] at hFint ⊢
      intro x hx
      obtain ⟨m', hm', rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hx
      rw [hcf]
      apply hFint
      exact MvPolynomial.coeff_mem_coeffs _ (by rw [← hcf]; exact MvPolynomial.mem_support_iff.1 hm')
    refine ⟨f, Submodule.mem_inf.2 ⟨hfpol, hfint⟩, ?_⟩
    have hfz : ∀ m ∈ (M.freeze p LL ρ n f).support, ∑ c, m (Fin.last N, c) = n := by
      intro m hm
      have := hom_freeze LL ρ n hS f hfpol (MvPolynomial.mem_support_iff.1 hm)
      rwa [weight_wL] at this
    have hG := vanish LL n ρ (M.freeze p LL ρ n f - F)
      (fun c hc => by rw [map_sub, freeze_inv LL ρ n f c hc, hinv c hc, sub_zero]) (fun m hkk => ?_)
    · exact sub_eq_zero.1 hG
    · rw [MvPolynomial.coeff_sub, sub_eq_zero]
      by_cases hrow : ∑ c, m (Fin.last N, c) = n
      · have hZ : ∀ c, c ≠ ρ → m (Fin.last N, c) = 0 := fun c hc => by
          simp only [kk] at hkk
          exact (Finset.sum_eq_zero_iff.1 hkk) c (Finset.mem_erase.2 ⟨hc, Finset.mem_univ _⟩)
        rw [eq_ext_res n ρ m hZ hrow, ← coeff_ev ρ n _ hfz, ← coeff_ev ρ n F hFn, ev_freeze, hf]
      · have h1 : coeff m (M.freeze p LL ρ n f) = 0 := by
          by_contra h
          exact hrow (hfz m (MvPolynomial.mem_support_iff.2 h))
        have h2 : coeff m F = 0 := by
          by_contra h
          exact hrow (hFn m (MvPolynomial.mem_support_iff.2 h))
        rw [h1, h2]
end Formalism.GM
