-- Prove2me | solution 2 for BookProof.HashimotoShiftInvert.exists_isShiftInvert
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:17:13.409841+00:00
-- url     : https://prove2.me/submissions/6692cfdd-9094-4e0f-aee7-e2b1d99d5c93

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterComplexShiftCore

set_option autoImplicit false

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem p2m_norm_shiftMap_ge_430 {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
    {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (x : Dom) :
    γ * ‖(x : F)‖ ≤ ‖shiftMap A γ x‖ := by
  have hre : (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re = quadForm A x + γ * ‖(x : F)‖ ^ 2 := by
    have happ : shiftMap A γ x = A x + (γ : ℂ) • (x : F) := rfl
    rw [happ, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.add_re]
    simp [quadForm, ← Complex.ofReal_pow]
  have h2 : (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re ≤ ‖(x : F)‖ * ‖shiftMap A γ x‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  rw [hre] at h2
  have hq := hpos x
  rcases eq_or_lt_of_le (norm_nonneg (x : F)) with h0 | hpx
  · rw [← h0]; simp
  · have : γ * ‖(x : F)‖ * ‖(x : F)‖ ≤ ‖shiftMap A γ x‖ * ‖(x : F)‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpx

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (hγ : 0 < γ) (hsurj : Function.Surjective (shiftMap A γ)) :
    ∃ R : F →L[ℂ] F, IsShiftInvert A γ R := by
  have hinj : Function.Injective (shiftMap A γ) := by
    intro x y hxy
    have h := p2m_norm_shiftMap_ge_430 hpos (γ := γ) (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at h
    have hx : ‖((x - y : Dom) : F)‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg ((x - y : Dom) : F)]) (norm_nonneg _)
    have hz : ((x - y : Dom) : F) = 0 := norm_eq_zero.mp hx
    have hz' : x - y = 0 := Subtype.ext (by simpa using hz)
    exact sub_eq_zero.mp hz'
  let f : Dom ≃ₗ[ℂ] F := LinearEquiv.ofBijective (shiftMap A γ) ⟨hinj, hsurj⟩
  have hf : ∀ x : Dom, f x = shiftMap A γ x := fun x => rfl
  let R0 : F →ₗ[ℂ] F := Dom.subtype ∘ₗ (f.symm : F →ₗ[ℂ] Dom)
  have hR0 : ∀ u : F, R0 u = ((f.symm u : Dom) : F) := fun u => rfl
  have hbound : ∀ u : F, ‖R0 u‖ ≤ γ⁻¹ * ‖u‖ := by
    intro u
    have h := p2m_norm_shiftMap_ge_430 hpos (γ := γ) (f.symm u)
    rw [← hf, LinearEquiv.apply_symm_apply] at h
    rw [hR0, le_inv_mul_iff₀ hγ]
    exact h
  refine ⟨LinearMap.mkContinuous R0 γ⁻¹ hbound, ?_, ?_⟩
  · intro x
    rw [LinearMap.mkContinuous_apply, hR0, ← hf, LinearEquiv.symm_apply_apply]
  · intro u
    refine ⟨by rw [LinearMap.mkContinuous_apply, hR0]; exact (f.symm u).2, ?_⟩
    have : (⟨(LinearMap.mkContinuous R0 γ⁻¹ hbound) u, by
        rw [LinearMap.mkContinuous_apply, hR0]; exact (f.symm u).2⟩ : Dom) = f.symm u := by
      apply Subtype.ext
      exact (LinearMap.mkContinuous_apply R0 γ⁻¹ hbound u).trans (hR0 u)
    rw [this, ← hf, LinearEquiv.apply_symm_apply]
