-- Prove2me | solution 1 for DbarRegularity.maximalFunction_distribution_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T22:45:06.787066+00:00
-- url     : https://prove2.me/submissions/8d1e83b9-2fc5-4095-9326-06e7bf564b3e

import Definitions.Def_DbarRegularity_Setting
import Theorems.Thm_DbarRegularity_maximalFunction_weakType_one
import Theorems.Thm_DbarRegularity_maximalFunction_le_indicator_add



namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal NNReal

/-- Distribution bound for the maximal function in terms of the large values of `f`. -/
theorem maximalFunction_distribution_le (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (α : ℝ≥0)
    (hα : 0 < α) :
    volume {x | (α : ℝ≥0∞) < maximalFunction f x} ≤
      2 * (5 : ℝ≥0∞) ^ d / α *
        ∫⁻ x, {y | (α : ℝ≥0∞) / 2 < ‖f y‖ₑ}.indicator (fun y => ‖f y‖ₑ) x := by
  set g := {y | (α : ℝ≥0∞) / 2 < ‖f y‖ₑ}.indicator f
  have hα2 : (0 : ℝ≥0) < α / 2 := by positivity
  have hcoe : ((α / 2 : ℝ≥0) : ℝ≥0∞) = (α : ℝ≥0∞) / 2 := by
    rw [ENNReal.coe_div two_ne_zero]; rfl
  have hsub : {x | (α : ℝ≥0∞) < maximalFunction f x} ⊆
      {x | ((α / 2 : ℝ≥0) : ℝ≥0∞) < maximalFunction g x} := by
    intro x hx
    simp only [mem_setOf_eq, hcoe] at hx ⊢
    have h1 := hx.trans_le (maximalFunction_le_indicator_add d f ((α : ℝ≥0∞) / 2) x)
    by_contra h
    push_neg at h
    have h3 := add_le_add h (le_refl ((α : ℝ≥0∞) / 2))
    rw [ENNReal.add_halves] at h3
    exact absurd h1 (not_lt.2 h3)
  have hg : ∀ y, ‖g y‖ₑ = {y | (α : ℝ≥0∞) / 2 < ‖f y‖ₑ}.indicator (fun y => ‖f y‖ₑ) y :=
    fun y => enorm_indicator_eq_indicator_enorm f y
  calc volume {x | (α : ℝ≥0∞) < maximalFunction f x}
      ≤ volume {x | ((α / 2 : ℝ≥0) : ℝ≥0∞) < maximalFunction g x} := measure_mono hsub
    _ ≤ (5 : ℝ≥0∞) ^ d / ((α / 2 : ℝ≥0) : ℝ≥0∞) * ∫⁻ x, ‖g x‖ₑ :=
        maximalFunction_weakType_one d g (α / 2) hα2
    _ = _ := by
        simp_rw [hg, hcoe]
        congr 1
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
          ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.2 two_ne_zero)) (Or.inl ENNReal.coe_ne_top),
          inv_inv]
        ring

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal

theorem solution (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (α : ℝ≥0)
    (hα : 0 < α) :
    volume {x | (α : ℝ≥0∞) < maximalFunction f x} ≤
      2 * (5 : ℝ≥0∞) ^ d / α *
        ∫⁻ x, {y | (α : ℝ≥0∞) / 2 < ‖f y‖ₑ}.indicator (fun y => ‖f y‖ₑ) x :=
  maximalFunction_distribution_le d f α hα
