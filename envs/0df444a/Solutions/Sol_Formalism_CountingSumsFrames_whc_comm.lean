-- Prove2me | solution 1 for Formalism.CountingSumsFrames.whc_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:44.397155+00:00
-- url     : https://prove2.me/submissions/f413ac7f-27ce-4ae4-8b03-121d661f6c02

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
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
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution {σ M : Type} [AddCommMonoid M] (w : σ → M) (A : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (hA : ∀ D x, x ∈ weightedHomogeneousSubmodule ℚ_[p] w D → A x ∈ weightedHomogeneousSubmodule ℚ_[p] w D)
    (D : M) (x : MvPolynomial σ ℚ_[p]) :
    weightedHomogeneousComponent w D (A x) = A (weightedHomogeneousComponent w D x) := by
  classical
  have hx : x = ∑ ν ∈ x.support.image (Finsupp.weight w), weightedHomogeneousComponent w ν x := by
    ext d
    rw [coeff_sum]
    simp only [coeff_weightedHomogeneousComponent]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (Finset.mem_image.mpr ⟨d, mem_support_iff.mpr hne, rfl⟩)
  conv_lhs => rw [hx]
  rw [map_sum, map_sum]
  have e : ∀ ν, weightedHomogeneousComponent w D (A (weightedHomogeneousComponent w ν x)) =
      if ν = D then A (weightedHomogeneousComponent w ν x) else 0 := fun ν => by
    rw [weightedHomogeneousComponent_of_mem (hA ν _ (weightedHomogeneousComponent_mem w x ν))]
    by_cases h : ν = D
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  simp only [e, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [weightedHomogeneousComponent_eq_zero', map_zero]
    intro d hd h'
    exact h (Finset.mem_image.mpr ⟨d, hd, h'⟩)
end Formalism.CountingSumsFrames
