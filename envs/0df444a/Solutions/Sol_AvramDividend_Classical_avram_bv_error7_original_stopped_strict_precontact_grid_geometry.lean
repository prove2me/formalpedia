-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_stopped_strict_precontact_grid_geometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:32:04.575025+00:00
-- url     : https://prove2.me/submissions/d1ebd77b-d4f2-47c5-bf6b-22b4d9081cb8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Every strict precontact prefix of an ordered stopped physical grid is again
an ordered grid with the same horizon; the zero-clock case is exact. -/
theorem solution
    {Ω : Type*} (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ) (T : ℝ≥0)
    (hGrid : ∀ m ω, u m 0 = 0 ∧ u m (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m i ≤ u m (i + 1))) :
    ∀ m ω, u m 0 = 0 ∧ u m (k m ω - 1) ≤ T ∧
      (∀ i, i < k m ω - 1 → u m i ≤ u m (i + 1)) := by
  intro m ω
  rcases hGrid m ω with ⟨hZero, hEnd, hMono⟩
  refine ⟨hZero, ?_, ?_⟩
  · by_cases h : k m ω = 0
    · simpa [h, hZero] using hEnd
    · have hPrev : k m ω - 1 < k m ω := by omega
      have hNext : k m ω - 1 + 1 = k m ω := by omega
      have hStep := hMono (k m ω - 1) hPrev
      rw [hNext] at hStep
      exact hStep.trans hEnd
  · intro i hi
    exact hMono i (lt_of_lt_of_le hi (Nat.sub_le _ _))
