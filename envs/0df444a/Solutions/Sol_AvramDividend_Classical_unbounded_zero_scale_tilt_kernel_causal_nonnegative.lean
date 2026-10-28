-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_zero_scale_tilt_kernel_causal_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:40:49.972985+00:00
-- url     : https://prove2.me/submissions/8ed4b7af-61ad-4b57-9d43-5f919c030bed

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The positive Esscher tilt of an unbounded-variation zero scale is causal and nonnegative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q θ : ℝ) (hq : 0 ≤ q) :
    (∀ x : ℝ, x ≤ 0 →
      q * (Real.exp (-(θ * x)) * W₀ x) = 0) ∧
    (∀ x : ℝ, 0 ≤
      q * (Real.exp (-(θ * x)) * W₀ x)) := by
  have hzero : W₀ 0 = 0 :=
    unbounded_scale_zero_origin_nonnegative_discount
      X hnbv 0 le_rfl W₀ hW₀
  constructor
  · intro x hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · simp [hW₀.1 x hlt]
    · subst x
      simp [hzero]
  · intro x
    by_cases hx : 0 ≤ x
    · exact mul_nonneg hq
        (mul_nonneg (le_of_lt (Real.exp_pos _)) (hW₀.2.1 x hx))
    · have hlt : x < 0 := lt_of_not_ge hx
      simp [hW₀.1 x hlt]
