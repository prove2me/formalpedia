-- Prove2me | solution 1 for AvramDividend.Classical.lower_survival_future_increment_pathwise_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:04:45.373493+00:00
-- url     : https://prove2.me/submissions/de588da8-b524-4e0f-8121-b297f4525fbd

import Mathlib.Data.NNReal.Basic
import Theorems.Thm_AvramDividend_Classical_lower_survival_closed_horizon_pathwise_split
import Theorems.Thm_AvramDividend_Classical_lower_survival_shifted_interval_reparam

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal
open AvramDividend.Classical

/-- Split continuous one-sided survival into past and stationary future increments. -/
theorem solution
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ) (x : ℝ) (s u : ℝ≥0) :
    {ω : Ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + Y v ω} =
      {ω : Ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + Y v ω} ∩
      {ω : Ω | ∀ v : ℝ≥0, v ≤ u →
        0 ≤ (x + Y s ω) + (Y (s + v) ω - Y s ω)} := by
  rw [lower_survival_closed_horizon_pathwise_split Y x s (s + u)
    (le_add_of_nonneg_right (show 0 ≤ u from zero_le))]
  ext ω
  constructor
  · rintro ⟨hPast, hFuture⟩
    exact ⟨hPast,
      (lower_survival_shifted_interval_reparam (fun t => Y t ω) x s u).mp hFuture⟩
  · rintro ⟨hPast, hFuture⟩
    exact ⟨hPast,
      (lower_survival_shifted_interval_reparam (fun t => Y t ω) x s u).mpr hFuture⟩
