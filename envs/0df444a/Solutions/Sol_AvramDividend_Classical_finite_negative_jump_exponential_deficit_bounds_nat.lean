-- Prove2me | solution 1 for AvramDividend.Classical.finite_negative_jump_exponential_deficit_bounds_nat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:30:55.298176+00:00
-- url     : https://prove2.me/submissions/7b3293b5-4a3a-4968-84c4-f6e1928ca964

import Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exponential_deficit_limit_nat
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.SpecialFunctions.Exp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The negative-jump Laplace deficit is nonnegative and bounded by the finite activity. -/
theorem solution
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) < ⊤)
    (n : ℕ) :
    0 ≤ (∫ y in Iio (0 : ℝ),
      (1 - Real.exp ((n : ℝ) * y)) ∂ν) ∧
    (∫ y in Iio (0 : ℝ),
      (1 - Real.exp ((n : ℝ) * y)) ∂ν) ≤
      (ν (Iio (0 : ℝ))).toReal := by
  let μ : Measure ℝ := ν.restrict (Iio (0 : ℝ))
  letI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ] using hFinite
  have hmem : ∀ᵐ y : ℝ ∂μ, y < 0 :=
    ae_restrict_mem measurableSet_Iio
  have hInt :
      Integrable (fun y : ℝ => Real.exp ((n : ℝ) * y)) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).measurable).aestronglyMeasurable
    · filter_upwards [hmem] with y hy
      have hy0 : (n : ℝ) * y ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_lt hy)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (Real.exp_le_one_iff).2 hy0
  have hSplit :
      (∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂ν) =
      (ν (Iio (0 : ℝ))).toReal -
        (∫ y in Iio (0 : ℝ), Real.exp ((n : ℝ) * y) ∂ν) := by
    change (∫ y : ℝ, (1 - Real.exp ((n : ℝ) * y)) ∂μ) =
      (ν (Iio (0 : ℝ))).toReal -
        (∫ y : ℝ, Real.exp ((n : ℝ) * y) ∂μ)
    rw [integral_sub (integrable_const _) hInt]
    simp [μ, Measure.real_def]
  have hLow :
      0 ≤ (∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂ν) := by
    apply setIntegral_nonneg measurableSet_Iio
    intro y hy
    have hy0 : (n : ℝ) * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_lt hy)
    exact sub_nonneg.mpr ((Real.exp_le_one_iff).2 hy0)
  have hExp :
      0 ≤ (∫ y in Iio (0 : ℝ), Real.exp ((n : ℝ) * y) ∂ν) := by
    apply setIntegral_nonneg measurableSet_Iio
    intro y hy
    exact le_of_lt (Real.exp_pos _)
  constructor
  · exact hLow
  · rw [hSplit]
    linarith
