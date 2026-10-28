-- Prove2me | solution 1 for AvramDividend.Classical.bv_drift_deficit_ae_monotone_on_countable_schedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:23:37.815962+00:00
-- url     : https://prove2.me/submissions/0310707b-2dd4-448b-94e2-9837c3c45c70

import Theorems.Thm_AvramDividend_Classical_bv_process_drift_compensated_increment_nonneg
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter
open scoped NNReal ENNReal

/-- A countable intersection turns fixed-pair increment bounds into a common monotone path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (r : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ i j : ℕ, r i ≤ r j →
      X.drift * (r i : ℝ) - X.X (r i) ω ≤
      X.drift * (r j : ℝ) - X.X (r j) ω := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : r i ≤ r j
  · filter_upwards
      [bv_process_drift_compensated_increment_nonneg X hBV (r i) (r j) hij]
      with ω hω hOrdered
    nlinarith
  · exact Filter.Eventually.of_forall (fun ω hOrdered => (hij hOrdered).elim)
