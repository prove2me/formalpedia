-- Prove2me | solution 1 for DbarRegularity.inv_sq_kernel_conditions
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T20:33:59.885516+00:00
-- url     : https://prove2.me/submissions/b4bbd9d2-74ef-47f8-9043-c50daf264b53

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Theorems.Thm_DbarRegularity_hormander_of_norm_fderiv_le



namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal ContDiff

/-- The kernel `1 / (y₀ + i y₁)²` on `ℝ²` satisfies Stein's size, Hörmander and cancellation
conditions for some constant `B`. -/
theorem inv_sq_kernel_conditions_aux (K : EuclideanSpace ℝ (Fin 2) → ℂ)
    (hK : ∀ y, K y = 1 / ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ^ 2) :
    ∃ B : ℝ, AEStronglyMeasurable K volume ∧
      (∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ 2) ∧
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B) ∧
      (∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0) := by
  set e := Complex.orthonormalBasisOneI.repr.symm with he_def
  have he : ∀ y, e y = (y 0 : ℂ) + (y 1 : ℂ) * Complex.I := fun y =>
    Complex.orthonormalBasisOneI_repr_symm_apply y
  have hKe : ∀ y, K y = (e y) ^ (-2 : ℤ) := by
    intro y
    rw [hK, he, zpow_neg, one_div]
    norm_cast
  have hne : ∀ y : EuclideanSpace ℝ (Fin 2), y ≠ 0 → e y ≠ 0 := fun y hy h =>
    hy (e.map_eq_zero_iff.1 h)
  have hnorm : ∀ y, ‖e y‖ = ‖y‖ := fun y => e.norm_map y
  -- derivative
  have hder : ∀ y : EuclideanSpace ℝ (Fin 2), y ≠ 0 →
      HasFDerivAt K (((-2 : ℤ) * (e y) ^ ((-2 : ℤ) - 1)) •
        (e.toLinearIsometry.toContinuousLinearMap)) y := by
    intro y hy
    have h1 := (hasDerivAt_zpow (-2) (e y) (Or.inl (hne y hy))).comp_hasFDerivAt y
      (e.toLinearIsometry.toContinuousLinearMap.hasFDerivAt)
    have hfun : K = (fun w : ℂ => w ^ (-2 : ℤ)) ∘ e.toLinearIsometry.toContinuousLinearMap := by
      funext z; rw [hKe]; rfl
    rw [hfun]
    exact h1
  have hCD : ContDiffOn ℝ 1 K {0}ᶜ := by
    intro y hy
    have : ContDiffAt ℝ 1 K y := by
      have hfun : K = fun z => ((e z) ^ 2)⁻¹ := by
        funext z; rw [hKe, zpow_neg]; norm_cast
      rw [hfun]
      exact (e.contDiff.contDiffAt.pow 2).inv (pow_ne_zero 2 (hne y hy))
    exact this.contDiffWithinAt
  have hbound : ∀ x : EuclideanSpace ℝ (Fin 2), x ≠ 0 → ‖fderiv ℝ K x‖ ≤ 2 / ‖x‖ ^ (2 + 1) := by
    intro x hx
    rw [(hder x hx).fderiv]
    have h2 : ‖((-2 : ℤ) : ℂ) * (e x) ^ ((-2 : ℤ) - 1)‖ = 2 / ‖x‖ ^ (2 + 1) := by
      rw [norm_mul, norm_zpow, hnorm]
      norm_num
      rw [div_eq_mul_inv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [ContinuousLinearMap.smul_apply, norm_smul, h2]
    change 2 / ‖x‖ ^ (2 + 1) * ‖e v‖ ≤ _
    rw [hnorm]
  obtain ⟨C, hC⟩ := hormander_of_norm_fderiv_le 2
  refine ⟨max 1 (C * 2), ?_, ?_, ?_, ?_⟩
  · have : K = (fun w : ℂ => w ^ (-2 : ℤ)) ∘ e := by funext z; rw [hKe]; rfl
    rw [this]
    exact (Measurable.comp (g := fun w : ℂ => w ^ (-2 : ℤ)) (by fun_prop)
      e.continuous.measurable).aestronglyMeasurable
  · intro x hx
    have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
    rw [hKe, norm_zpow, hnorm, zpow_neg, zpow_ofNat, ← one_div]
    gcongr
    exact le_max_left _ _
  · intro y hy
    exact (hC 2 K hCD hbound y hy).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  · intro R₁ R₂ _ _
    -- rotation by a quarter turn
    set ρ : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      (e.trans (rotation (Circle.exp (Real.pi / 2)))).trans e.symm
      with hρ
    have hρe : ∀ y, e (ρ y) = Complex.I * e y := by
      intro y
      simp only [hρ, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
      simp [rotation_apply, Circle.coe_exp, Complex.exp_pi_div_two_mul_I]
    have hKρ : ∀ y, K (ρ y) = - K y := by
      intro y
      rw [hKe, hKe, hρe, mul_zpow]
      have : Complex.I ^ (-2 : ℤ) = -1 := by
        rw [zpow_neg, zpow_ofNat, Complex.I_sq]; norm_num
      rw [this, neg_one_mul]
    set S : Set (EuclideanSpace ℝ (Fin 2)) := {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂} with hS
    have hpre : ρ ⁻¹' S = S := by
      ext x; simp [hS, ρ.norm_map]
    have hmp := ρ.measurePreserving
    have key := hmp.setIntegral_preimage_emb ρ.toHomeomorph.measurableEmbedding K S
    rw [hpre] at key
    simp only [hKρ, integral_neg] at key
    linear_combination (-1 / 2 : ℂ) * key

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal ContDiff

theorem solution (K : EuclideanSpace ℝ (Fin 2) → ℂ)
    (hK : ∀ y, K y = 1 / ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ^ 2) :
    ∃ B : ℝ, AEStronglyMeasurable K volume ∧
      (∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ 2) ∧
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B) ∧
      (∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0) :=
  inv_sq_kernel_conditions_aux K hK
