-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_tenth_horizon_uniform_original_physical_grid_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:14:01.339188+00:00
-- url     : https://prove2.me/submissions/c3889672-0db7-47d7-b312-58673832e52a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_prescribed_uniform_physical_grid_is_monotone_and_has_exact_last_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical AvramDividend.Classical
open scoped NNReal
theorem solution :
    let u : ℕ → ℕ → ℝ≥0 := fun n i =>
      ⟨(1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
    (∀ n, u n 0 = 0 ∧
      (u n (n + 1) : ℝ) =
        (1 / 10 : ℝ) - (1 / 10 : ℝ) / ((n : ℝ) + 2)) ∧
    (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
    (∀ n i, (u n i : ℝ) = (1 / 10 : ℝ) *
      (i : ℝ) / ((n : ℝ) + 2)) := by
  let u : ℕ → ℕ → ℝ≥0 := fun n i =>
    ⟨(1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
  have h0 : ∀ n, u n 0 = 0 := by
    intro n
    apply Subtype.ext
    norm_num [u]
  have hUniform : ∀ n i, (u n i : ℝ) =
      (1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2) := by
    intro n i
    rfl
  have hGrid :=
    avram_bva_a22_original_prescribed_uniform_physical_grid_is_monotone_and_has_exact_last_clock
      (1 / 10 : ℝ) (by norm_num) u h0 hUniform
  exact ⟨hGrid.1, hGrid.2, hUniform⟩
