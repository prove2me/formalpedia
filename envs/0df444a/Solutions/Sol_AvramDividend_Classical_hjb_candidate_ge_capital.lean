-- Prove2me | solution 1 for AvramDividend.Classical.hjb_candidate_ge_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T23:26:22.620991+00:00
-- url     : https://prove2.me/submissions/f5445834-d9a5-4d88-a247-6c78f32f38b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_derivative_floor_implies_linear_growth

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) :
    x ≤ w x := by
  have hcap : ∀ y ∈ Ioo (0 : ℝ) x, ENNReal.ofReal y < C := by
    intro y hy
    have hy0 : 0 ≤ y := le_of_lt hy.1
    exact lt_of_lt_of_le
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hy0).2 hy.2) hxc
  have hdiffCap :
      DifferentiableOn ℝ w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    by_cases hvar : X.BoundedVariation
    · exact (hw_smooth.2 hvar).differentiableOn (by norm_num)
    · exact (hw_smooth.1 hvar).differentiableOn (by norm_num)
  have hdiff : DifferentiableOn ℝ w (Ioo (0 : ℝ) x) :=
    hdiffCap.mono (by
      intro y hy
      exact ⟨hy.1, hcap y hy⟩)
  have hcont : ContinuousOn w (Icc (0 : ℝ) x) := by
    apply hw_cont.mono
    intro y hy
    exact hy.1
  have hderiv : ∀ y ∈ Ioo (0 : ℝ) x, 1 ≤ deriv w y := by
    intro y hy
    have heq := (hw_hjb y hy.1 (hcap y hy)).2
    have hmax := le_max_right
      (X.generator w y - q * w y) (1 - deriv w y)
    rw [heq] at hmax
    linarith
  exact derivative_floor_implies_linear_growth
    w x hx hcont hdiff hderiv hw0
