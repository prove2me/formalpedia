-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_levy_drift_increment_ae_schedule_pairs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:18:22.903316+00:00
-- url     : https://prove2.me/submissions/6c0d6a01-2345-4eb7-bc4f-d04e651ea770

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_increment_ae_fixed_times
import Mathlib.MeasureTheory.OuterMeasure.AE

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- A common probability-one set satisfies the drift inequality on every ordered schedule pair. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (ts : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ i j : ℕ, ts i ≤ ts j →
      X.X (ts j) ω - X.X (ts i) ω ≤
        ((ts j - ts i : ℝ≥0) : ℝ) * X.drift := by
  have hpair (i j : ℕ) :
      ∀ᵐ ω ∂P, ts i ≤ ts j →
        X.X (ts j) ω - X.X (ts i) ω ≤
          ((ts j - ts i : ℝ≥0) : ℝ) * X.drift := by
    by_cases hij : ts i ≤ ts j
    · exact (bv_actual_levy_drift_increment_ae_fixed_times
        X hBV (ts i) (ts j) hij).mono (fun ω hw _ => hw)
    · exact Filter.Eventually.of_forall (fun ω h => (hij h).elim)
  exact ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hpair i j))
