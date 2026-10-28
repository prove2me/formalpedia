-- Prove2me | solution 2 for AvramDividend.Classical.bv_infinite_activity_deficit_positive_all_times
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:29:52.885689+00:00
-- url     : https://prove2.me/submissions/85b314cc-35f4-4ff2-a3a0-8e6ad424ccd2

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_positive_grid
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Positivity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      0 < X.drift * (t : ℝ) - X.X t ω := by
  have hgrid : ∀ n : ℕ, 0 < (1 / ((n : ℝ≥0) + 1)) := fun n => by positivity
  filter_upwards [bv_infinite_activity_deficit_positive_grid X hBV hνinf
      (fun n : ℕ => 1 / ((n : ℝ≥0) + 1)) hgrid,
    bv_drift_deficit_ae_monotone_all_times X hBV] with ω hg hm t ht
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
  exact lt_of_lt_of_le (hg n) (hm (by simpa using hn.le))
