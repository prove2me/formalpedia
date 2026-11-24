-- Prove2me | solution 1 for Formalism.CountingSumsFrames.freeze_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:18.748929+00:00
-- url     : https://prove2.me/submissions/a94fab14-994d-4a7f-bcff-364019bad0f6

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_wL
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_freeze_inv
import Theorems.Thm_Formalism_GM_M_FB_coeff_ev
import Theorems.Thm_Formalism_GM_M_FB_eq_ext_res
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ev_freeze
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_freeze_inv
import Theorems.Thm_Formalism_GM_M_FB_hom_freeze
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_M_FB_vanish
import Theorems.Thm_Formalism_GM_M_FB_weight_wL
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
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters K) (ρ : Fin r) (n : ℕ) (hS : LL.total ≤ n)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hFpol' : F ∈ Pol p r (LL.snoc n))
    (hinv : IsFrozenInv p LL ρ n F) :
    ∃ f ∈ Pol p r LL, freeze p LL ρ n f = F ∧ ∀ m', coeff m' f = coeff (FB.ext n ρ m') F := by
  have hFrow : ∀ m ∈ F.support, ∑ c, m (Fin.last K, c) = n := fun m hm => by
    have h : MultiDeg (LL.snoc n) m := hFpol' (Finset.mem_coe.mpr hm)
    simpa using h (Fin.last K)
  have hcoeff := FB.coeff_ev ρ n F hFrow
  have hfpol : FB.ev p ρ F ∈ Pol p r LL := by
    rw [Pol, mem_restrictSupport_iff]
    intro m' hm'
    rw [Finset.mem_coe, mem_support_iff, hcoeff] at hm'
    have h : MultiDeg (LL.snoc n) (FB.ext n ρ m') := hFpol' (Finset.mem_coe.mpr (mem_support_iff.mpr hm'))
    intro i
    simpa using h (Fin.castSucc i)
  refine ⟨FB.ev p ρ F, hfpol, ?_, hcoeff⟩
  have hFhom : IsWeightedHomogeneous (FB.wL K r) F n := fun m hm => by
    rw [FB.weight_wL]; exact hFrow m (mem_support_iff.mpr hm)
  have hGhom : IsWeightedHomogeneous (FB.wL K r) (F - freeze p LL ρ n (FB.ev p ρ F)) n :=
    hFhom.sub (FB.hom_freeze LL ρ n hS _ hfpol)
  have hGrow : ∀ m ∈ (F - freeze p LL ρ n (FB.ev p ρ F)).support, ∑ c, m (Fin.last K, c) = n :=
    fun m hm => by rw [← FB.weight_wL]; exact hGhom (mem_support_iff.mp hm)
  have hGev : FB.ev p ρ (F - freeze p LL ρ n (FB.ev p ρ F)) = 0 := by
    rw [map_sub, FB.ev_freeze, sub_self]
  have hGinv : IsFrozenInv p LL ρ n (F - freeze p LL ρ n (FB.ev p ρ F)) := fun c hc => by
    rw [map_sub, hinv c hc, FB.freeze_inv LL ρ n _ c hc, sub_self]
  have h0 : ∀ m, FB.kk ρ m = 0 → coeff m (F - freeze p LL ρ n (FB.ev p ρ F)) = 0 := by
    intro m hm
    by_contra hne
    have hrow := hGrow m (mem_support_iff.mpr hne)
    have hZ : ∀ c, c ≠ ρ → m (Fin.last K, c) = 0 := fun c hc =>
      Finset.sum_eq_zero_iff.mp hm c (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩)
    apply hne
    rw [FB.eq_ext_res n ρ m hZ hrow, ← FB.coeff_ev ρ n _ hGrow, hGev, coeff_zero]
  exact (sub_eq_zero.mp (FB.vanish LL n ρ _ hGinv h0)).symm
end Formalism.CountingSumsFrames
