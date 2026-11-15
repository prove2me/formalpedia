-- Prove2me | solution 1 for AvramDividend.Classical.counting_delta_indicator_mean_and_pointwise_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:40:55.052633+00:00
-- url     : https://prove2.me/submissions/3279ec7c-aa21-458d-b859-e9ae88a12227

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
noncomputable section
theorem solution :
    (∀ n : ℕ, (∫ k : ℕ, ({n} : Set ℕ).indicator (fun _ => (1 : ℝ)) k
      ∂(Measure.count : Measure ℕ)) = 1) ∧
    (∀ k : ℕ, Tendsto (fun n : ℕ => ({n} : Set ℕ).indicator
      (fun _ => (1 : ℝ)) k) atTop (nhds 0)) := by
  constructor
  · intro n
    change (∫ k : ℕ, ({n} : Set ℕ).indicator (1 : ℕ → ℝ) k
      ∂(Measure.count : Measure ℕ)) = 1
    rw [integral_indicator_one (measurableSet_singleton n)]
    simp [Measure.real]
  · intro k
    have hz : ∀ᶠ n in atTop, ({n} : Set ℕ).indicator (fun _ => (1 : ℝ)) k = 0 := by
      filter_upwards [eventually_gt_atTop k] with n hn
      simp [Set.indicator, ne_of_lt hn]
    exact tendsto_const_nhds.congr' (hz.mono fun _ hn => hn.symm)
