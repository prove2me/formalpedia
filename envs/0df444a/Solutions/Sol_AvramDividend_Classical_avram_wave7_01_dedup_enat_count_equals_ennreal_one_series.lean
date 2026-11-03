-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_dedup_enat_count_equals_ennreal_one_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:02:47.934594+00:00
-- url     : https://prove2.me/submissions/ce9ca3b6-3608-4b9d-b135-c836ea93c19b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Any distinct active candidate-time enumeration has exactly its indicator
series as the extended natural cardinal count of its actual time image. -/
theorem solution
    (time : ℕ → ℝ≥0) (A : Set ℕ)
    (hInj : Set.InjOn time A) :
    ((time '' A).encard : ℝ≥0∞) =
      ∑' k : ℕ, if k ∈ A then (1 : ℝ≥0∞) else 0 := by
  classical
  calc
    ((time '' A).encard : ℝ≥0∞) = (A.encard : ℝ≥0∞) := by
      exact congrArg (fun n : ℕ∞ => (n : ℝ≥0∞)) hInj.encard_image
    _ = ∑' k : A, (1 : ℝ≥0∞) :=
      (ENNReal.tsum_set_one A).symm
    _ = ∑' k : ℕ,
          A.indicator (fun _ : ℕ => (1 : ℝ≥0∞)) k := by
      exact tsum_subtype A (fun _ : ℕ => (1 : ℝ≥0∞))
    _ = ∑' k : ℕ, if k ∈ A then (1 : ℝ≥0∞) else 0 := by
      apply tsum_congr
      intro k
      by_cases hk : k ∈ A
      · simp [Set.indicator, hk]
      · simp [Set.indicator, hk]
