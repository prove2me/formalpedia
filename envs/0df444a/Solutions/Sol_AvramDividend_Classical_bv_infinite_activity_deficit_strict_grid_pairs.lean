-- Prove2me | solution 1 for AvramDividend.Classical.bv_infinite_activity_deficit_strict_grid_pairs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:47:45.219666+00:00
-- url     : https://prove2.me/submissions/ef51a658-c843-49d1-b1de-4d858e500bd8

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_increment_strict_ae
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- One common null-set removal makes the infinite-activity deficit strictly increase along every grid pair. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (grid : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ i j : ℕ, grid i < grid j →
      X.drift * (grid i : ℝ) - X.X (grid i) ω <
        X.drift * (grid j : ℝ) - X.X (grid j) ω := by
  apply (ae_all_iff).mpr
  intro i
  apply (ae_all_iff).mpr
  intro j
  by_cases hij : grid i < grid j
  · filter_upwards
      [bv_infinite_activity_drift_deficit_increment_strict_ae
        X hBV hνinf (grid i) (grid j) hij]
      with ω hlt
    exact fun _ => hlt
  · filter_upwards with ω
    intro hlt
    exact False.elim (hij hlt)
