-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.smith_bases
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:00.093867+00:00
-- url     : https://prove2.me/submissions/db52652c-2c25-4b74-bb13-1fe3732e83b0

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_int_smul_mem
import Theorems.Thm_Formalism_GM_DetBound_norm_inv_entry_le
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
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution {σ : Type} (nb : ℕ) (f : Fin nb → MvPolynomial σ ℚ_[p])
    (Lat : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (hli : LinearIndependent ℤ_[p] f) (hsp : Submodule.span ℤ_[p] (Set.range f) = Lat)
    (B : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p])
    (U V : Matrix (Fin nb) (Fin nb) ℚ_[p]) (dg : Fin nb → ℚ_[p])
    (hU : ∀ x y, ‖U x y‖ ≤ 1) (hV : ∀ x y, ‖V x y‖ ≤ 1) (hUd : ‖U.det‖ = 1) (hVd : ‖V.det‖ = 1)
    (hfac : (Matrix.of fun x y => B (f x) (f y)) = U * Matrix.diagonal dg * V) :
    ∃ f' f'' : Fin nb → MvPolynomial σ ℚ_[p], (∀ a, f' a ∈ Lat) ∧ (∀ a, f'' a ∈ Lat) ∧
      LinearIndependent ℚ_[p] f' ∧ Lat ≤ Submodule.span ℤ_[p] (Set.range f') ∧
      ∀ a b, B (f' a) (f'' b) = if a = b then dg a else 0 := by
  classical
  have hUu : IsUnit U.det := by
    rw [isUnit_iff_ne_zero]; intro h; rw [h, norm_zero] at hUd; exact zero_ne_one hUd
  have hVu : IsUnit V.det := by
    rw [isUnit_iff_ne_zero]; intro h; rw [h, norm_zero] at hVd; exact zero_ne_one hVd
  have hUi := fun x y => DetBound.norm_inv_entry_le U hU hUd x y
  have hVi := fun x y => DetBound.norm_inv_entry_le V hV hVd x y
  have hliQ : LinearIndependent ℚ_[p] f := (LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]).mp hli
  have hfL : ∀ x, f x ∈ Lat := fun x => hsp ▸ Submodule.subset_span ⟨x, rfl⟩
  have hback : ∀ x, f x = ∑ a, U x a • ∑ y, U⁻¹ a y • f y := by
    intro x
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have : ∀ y, ∑ a, U x a * U⁻¹ a y = (1 : Matrix (Fin nb) (Fin nb) ℚ_[p]) x y := by
      intro y
      rw [← Matrix.mul_nonsing_inv U hUu, Matrix.mul_apply]
    simp only [this, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨fun a => ∑ x, U⁻¹ a x • f x, fun b => ∑ y, V⁻¹ y b • f y, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a => Lat.sum_mem fun x _ => int_smul_mem Lat _ (hUi a x) _ (hfL x)
  · exact fun b => Lat.sum_mem fun y _ => int_smul_mem Lat _ (hVi y b) _ (hfL y)
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Finset.smul_sum, smul_smul] at hg
    rw [Finset.sum_comm] at hg
    simp only [← Finset.sum_smul] at hg
    have h0 := Fintype.linearIndependent_iff.mp hliQ _ hg
    have h1 : Matrix.vecMul g U⁻¹ = 0 := by
      funext x
      simpa [Matrix.vecMul, dotProduct] using h0 x
    have h2 : Matrix.vecMul (Matrix.vecMul g U⁻¹) U = g := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul U hUu, Matrix.vecMul_one]
    intro a
    rw [← h2, h1, Matrix.zero_vecMul]; rfl
  · rw [← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hback x]
    exact Submodule.sum_mem _ fun a _ => int_smul_mem _ _ (hU x a) _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro a b
    have e : B (∑ x, U⁻¹ a x • f x) (∑ y, V⁻¹ y b • f y) =
        (U⁻¹ * (Matrix.of fun x y => B (f x) (f y)) * V⁻¹) a b := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply,
        Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [e, hfac]
    have : U⁻¹ * (U * Matrix.diagonal dg * V) * V⁻¹ = Matrix.diagonal dg := by
      rw [Matrix.mul_assoc U, ← Matrix.mul_assoc U⁻¹, Matrix.nonsing_inv_mul U hUu, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv V hVu, Matrix.mul_one]
    rw [this, Matrix.diagonal_apply]
end Formalism.CountingSumsFrames.TO
