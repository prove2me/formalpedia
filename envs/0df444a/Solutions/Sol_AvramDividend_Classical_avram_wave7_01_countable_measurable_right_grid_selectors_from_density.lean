-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_countable_measurable_right_grid_selectors_from_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:04:45.447381+00:00
-- url     : https://prove2.me/submissions/687c6d0b-c605-4960-99ad-a6f7530bbafb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_right_grid_selector_for_jump_marks

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Borel selectors at every precision for one path-dependent time. -/
theorem solution
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (t : (ℝ≥0 → ℝ) → ℝ≥0) (ht : Measurable t)
    (ε : ℕ → ℝ≥0) (hε : ∀ n, 0 < ε n) :
    ∃ index : ℕ → (ℝ≥0 → ℝ) → ℕ,
      (∀ n : ℕ, Measurable (index n)) ∧
      ∀ (n : ℕ) (Y : ℝ≥0 → ℝ),
        t Y < grid (index n Y) ∧
        grid (index n Y) < t Y + ε n := by
  have hExist (n : ℕ) (Y : ℝ≥0 → ℝ) :
      ∃ m : ℕ, t Y < grid m ∧ grid m < t Y + ε n := by
    have hInt : t Y < t Y + ε n := lt_add_of_pos_right _ (hε n)
    obtain ⟨v, ⟨m, rfl⟩, hv⟩ := hdense.exists_between hInt
    exact ⟨m, hv⟩
  have hSelector (n : ℕ) :
      ∃ q : (ℝ≥0 → ℝ) → ℕ, Measurable q ∧
        ∀ Y, t Y < grid (q Y) ∧ grid (q Y) < t Y + ε n :=
    avram_wave7_01_measurable_right_grid_selector_for_jump_marks
      grid t ht (ε n) (hExist n)
  choose q hMeas hBounds using hSelector
  exact ⟨q, hMeas, hBounds⟩
