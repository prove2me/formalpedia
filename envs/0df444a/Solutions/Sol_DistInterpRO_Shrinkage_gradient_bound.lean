-- Prove2me | solution 1 for DistInterpRO.Shrinkage.gradient_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:59:42.95526+00:00
-- url     : https://prove2.me/submissions/23393a85-d193-495f-ac5a-36b599153662

import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

/-- Polarization bound for a symmetric bilinear form with bounded quadratic form. -/
theorem aux_gb_polar {m : ℕ}
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (h : ℝ)
    (hsymm : ∀ v w, B v w = B w v) (hq : ∀ y, |B y y| ≤ h * ‖y‖ ^ 2)
    (x y : EuclideanSpace ℝ (Fin m)) :
    |B x y| ≤ h * (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  have e : B (x + y) (x + y) - B (x - y) (x - y) = 4 * B x y := by
    simp only [map_add, map_sub, add_apply, sub_apply]
    rw [hsymm y x]; ring
  have par : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have := parallelogram_law_with_norm ℝ x y
    nlinarith [this]
  have h1 := hq (x + y)
  have h2 := hq (x - y)
  have : |4 * B x y| ≤ h * ‖x + y‖ ^ 2 + h * ‖x - y‖ ^ 2 := by
    rw [← e]
    calc |B (x + y) (x + y) - B (x - y) (x - y)|
        ≤ |B (x + y) (x + y)| + |B (x - y) (x - y)| := abs_sub _ _
      _ ≤ _ := add_le_add h1 h2
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)] at this
  have hs : h * ‖x + y‖ ^ 2 + h * ‖x - y‖ ^ 2 = 2 * h * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    rw [← mul_add, par]; ring
  linarith

theorem aux_gb_bilin {m : ℕ}
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (h : ℝ) (hh : 0 ≤ h)
    (hsymm : ∀ v w, B v w = B w v) (hq : ∀ y, |B y y| ≤ h * ‖y‖ ^ 2) :
    ‖B‖ ≤ h := by
  refine ContinuousLinearMap.opNorm_le_bound₂ B hh ?_
  intro x y
  rw [Real.norm_eq_abs]
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have key := aux_gb_polar B h hsymm hq (‖x‖⁻¹ • x) (‖y‖⁻¹ • y)
  rw [norm_smul, norm_smul, norm_inv, norm_norm, norm_inv, norm_norm,
    inv_mul_cancel₀ hxn.ne', inv_mul_cancel₀ hyn.ne'] at key
  simp only [map_smul, smul_apply, smul_eq_mul] at key
  rw [abs_mul, abs_mul, abs_inv, abs_inv, abs_norm, abs_norm] at key
  have : |B x y| = ‖x‖ * ‖y‖ * (‖y‖⁻¹ * (‖x‖⁻¹ * |B x y|)) := by
    field_simp
  rw [this]
  have hpos : 0 ≤ ‖x‖ * ‖y‖ := by positivity
  calc ‖x‖ * ‖y‖ * (‖y‖⁻¹ * (‖x‖⁻¹ * |B x y|)) ≤ ‖x‖ * ‖y‖ * h := by
        apply mul_le_mul_of_nonneg_left _ hpos
        linarith [key]
    _ = h * ‖x‖ * ‖y‖ := by ring

end DistInterpRO.Shrinkage

open DistInterpRO.Shrinkage
open MeasureTheory
open scoped Pointwise

theorem solution {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (h : ℝ) (hh : 0 ≤ h) (hf : HasBoundedHessian (f v) h) :
    (∀ a b : EuclideanSpace ℝ (Fin m),
        ‖fderiv ℝ (f v) a - fderiv ℝ (f v) b‖ ≤ h * ‖a - b‖) ∧
    ∀ (Δ : Set (EuclideanSpace ℝ (Fin m))), IsCompact Δ →
      ∀ (α : ℝ), 0 < α → α < 1 →
      ∀ (x₀ x₁ : EuclideanSpace ℝ (Fin m)), x₁ ∈ Δ →
      ∀ β ∈ Set.Icc (0 : ℝ) 1, ∀ β' ∈ Set.Icc (0 : ℝ) 1,
        ‖fderiv ℝ (f v) (x₀ + β • x₁) - fderiv ℝ (f v) (x₀ + (α * β') • x₁)‖ ≤
            h * ‖β • x₁ - (α * β') • x₁‖ ∧
          h * ‖β • x₁ - (α * β') • x₁‖ ≤ h * ‖x₁‖ ∧
          h * ‖x₁‖ ≤ h * devRadius Δ := by
  obtain ⟨hd1, hd2, hq⟩ := hf
  have hnorm : ∀ x, ‖fderiv ℝ (fderiv ℝ (f v)) x‖ ≤ h := by
    intro x
    apply aux_gb_bilin _ h hh
    · intro a b
      exact second_derivative_symmetric (f := f v) (fun y => (hd1 y).hasFDerivAt)
        (hd2 x).hasFDerivAt a b
    · exact hq x
  have lip : ∀ a b : EuclideanSpace ℝ (Fin m),
      ‖fderiv ℝ (f v) a - fderiv ℝ (f v) b‖ ≤ h * ‖a - b‖ := by
    intro a b
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ)
      (fun x _ => hd2 x) (fun x _ => hnorm x) convex_univ (Set.mem_univ b) (Set.mem_univ a)
  refine ⟨lip, ?_⟩
  intro Δ hΔ α hα0 hα1 x₀ x₁ hx₁ β hβ β' hβ'
  refine ⟨?_, ?_, ?_⟩
  · have := lip (x₀ + β • x₁) (x₀ + (α * β') • x₁)
    simpa [add_sub_add_left_eq_sub] using this
  · apply mul_le_mul_of_nonneg_left _ hh
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have hab : |β - α * β'| ≤ 1 := by
      obtain ⟨hb0, hb1⟩ := hβ
      obtain ⟨hc0, hc1⟩ := hβ'
      have h1 : 0 ≤ α * β' := mul_nonneg hα0.le hc0
      have h2 : α * β' ≤ 1 := by nlinarith
      rw [abs_le]; constructor <;> linarith
    calc |β - α * β'| * ‖x₁‖ ≤ 1 * ‖x₁‖ :=
          mul_le_mul_of_nonneg_right hab (norm_nonneg _)
      _ = ‖x₁‖ := one_mul _
  · apply mul_le_mul_of_nonneg_left _ hh
    unfold devRadius
    apply le_csSup
    · exact (hΔ.image continuous_norm).bddAbove
    · exact ⟨x₁, hx₁, rfl⟩
