-- Prove2me | solution 2 for AvramDividend.Classical.bv_infinite_activity_deficit_strict_grid_pairs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:47:57.9648+00:00
-- url     : https://prove2.me/submissions/33333673-a531-4881-93b0-93f1f18408f1

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_increment_strict_ae
import Mathlib.MeasureTheory.OuterMeasure.AE

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

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
  rw [ae_all_iff]; intro i
  rw [ae_all_iff]; intro j
  by_cases hij : grid i < grid j
  · filter_upwards [bv_infinite_activity_drift_deficit_increment_strict_ae X hBV hνinf _ _ hij]
      with ω h _ using h
  · exact Filter.Eventually.of_forall (fun ω h => absurd h hij)
