-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_grid_binary_coverage_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:53:06.386155+00:00
-- url     : https://prove2.me/submissions/99c7d3ef-6eaf-4855-a5a7-d47dede280dc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_increment_ae_schedule_pairs

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ i : ℕ, i < n →
      (X.X (t (i + 1)) ω - X.X (t i) ω <
        X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))) ∨
      (X.X (t (i + 1)) ω - X.X (t i) ω =
        X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))) := by
  filter_upwards [bv_actual_levy_drift_increment_ae_schedule_pairs X hBV t]
    with ω hp
  intro i hi
  have hle := hp i (i + 1) (ht (Nat.le_succ i))
  have hle' : X.X (t (i + 1)) ω - X.X (t i) ω ≤
      X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)) := by
    nlinarith [hle]
  exact lt_or_eq_of_le hle'
