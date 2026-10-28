-- Prove2me | solution 1 for AvramDividend.Classical.bv_infinite_activity_deficit_positive_all_times_of_cofinal_grid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:27:47.627705+00:00
-- url     : https://prove2.me/submissions/efb870ed-6cf0-47aa-979f-03411d0fe8f8

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_positive_grid
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.MeasureTheory.OuterMeasure.AE

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (grid : ℕ → ℝ≥0)
    (hgrid : ∀ n, 0 < grid n)
    (hbelow : ∀ t : ℝ≥0, 0 < t → ∃ n, grid n ≤ t) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      0 < X.drift * (t : ℝ) - X.X t ω := by
  filter_upwards [bv_infinite_activity_deficit_positive_grid X hBV hνinf grid hgrid,
    bv_drift_deficit_ae_monotone_all_times X hBV] with ω hg hm t ht
  obtain ⟨n, hn⟩ := hbelow t ht
  exact lt_of_lt_of_le (hg n) (hm hn)
