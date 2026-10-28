-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_grid_residual_active_pattern_product_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:03:47.719249+00:00
-- url     : https://prove2.me/submissions/fead9ae6-b2f0-4e10-b98d-35925bdecfbf

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_all_finite_prefix_increment_cylinder_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Every prescribed finite active/inactive residual-cell pattern factorises. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (active : Finset ℕ) :
    P {ω : Ω | ∀ i : ℕ, i < n →
      X.X (t (i + 1)) ω - X.X (t i) ω ∈
        (if i ∈ active then
          Iio (X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))
        else
          {X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))})} =
    ∏ i ∈ Finset.range n,
      P {ω : Ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈
        (if i ∈ active then
          Iio (X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))
        else
          {X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))})} := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let B : ℕ → Set ℝ := fun i =>
    if i ∈ active then
      Iio (X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))
    else
      {X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))}
  have hB : ∀ i, MeasurableSet (B i) := by
    intro i
    dsimp [B]
    split_ifs
    · exact measurableSet_Iio
    · exact measurableSet_singleton _
  have h := AvramDividend.Classical.chat04_all_finite_prefix_increment_cylinder_product
    X 0 Set.univ (by simp) t ht bot_le B hB n
  simpa [B] using h
