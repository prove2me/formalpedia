-- Prove2me | solution 1 for AvramDividend.Classical.bv_infinite_activity_deficit_positive_all_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:28:42.175002+00:00
-- url     : https://prove2.me/submissions/f226855e-6c95-4db5-9ef6-54b9caf64427

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_positive_grid
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Infinite negative activity makes the actual drift deficit positive at every positive time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      0 < X.drift * (t : ℝ) - X.X t ω := by
  let grid : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  have hPosGrid : ∀ n : ℕ, 0 < grid n := by
    intro n
    dsimp [grid]
    positivity
  have hBelow : ∀ t : ℝ≥0, 0 < t → ∃ n, grid n ≤ t := by
    intro t ht
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
    exact ⟨n, le_of_lt hn⟩
  filter_upwards
    [bv_infinite_activity_deficit_positive_grid X hBV hνinf grid hPosGrid,
      bv_drift_deficit_ae_monotone_all_times X hBV]
    with ω hGrid hMono
  intro t ht
  obtain ⟨n, hn⟩ := hBelow t ht
  exact lt_of_lt_of_le (hGrid n) (hMono hn)
