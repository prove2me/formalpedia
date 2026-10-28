-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_threshold_increment_budget_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:25:36.200323+00:00
-- url     : https://prove2.me/submissions/0c4b67d4-c4a0-4f8e-8b30-a37f0ca25eeb

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_bv_actual_path_partition_variation_bound_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every finite partition of an actual BV Lévy path has at most its
variation budget divided by epsilon many epsilon-sized increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
      ∀ (n : ℕ) (ε : ℝ), 0 < ε →
      (∑ i ∈ Finset.range n,
        if ε ≤ |X.X (u (i + 1)) ω - X.X (u i) ω|
        then ε else 0) ≤
      2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
        (X.X (u n) ω - X.X (u 0) ω) := by
  filter_upwards
    [bv_actual_path_partition_variation_bound_ws01b X hX hBV]
      with ω hVar
  intro u hu n ε hε
  calc
    (∑ i ∈ Finset.range n,
      if ε ≤ |X.X (u (i + 1)) ω - X.X (u i) ω|
      then ε else 0) ≤
      ∑ i ∈ Finset.range n,
        |X.X (u (i + 1)) ω - X.X (u i) ω| := by
          apply Finset.sum_le_sum
          intro i hi
          split_ifs with h
          · exact h
          · exact abs_nonneg _
    _ ≤ 2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
          (X.X (u n) ω - X.X (u 0) ω) :=
      hVar u hu n
