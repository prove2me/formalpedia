-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_uniform_finite_selected_indices_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:11:54.504519+00:00
-- url     : https://prove2.me/submissions/3995ebd7-6737-4d5a-aeab-a297e30c4baa

import Mathlib.Data.Finset.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_finite_selected_cells_eventually_injective
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_selected_cell_indices_eventually_distinct
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped NNReal

/-- All selected cells around a finite set of distinct original jump times
are eventually injective if their right endpoints converge to those times. -/
theorem solution
    (F : Finset ℝ≥0) (idx : ℝ≥0 → ℕ → ℕ) (w : ℕ → ℝ≥0)
    (hright : ∀ t ∈ F,
      Tendsto (fun n : ℕ => (((idx t n + 1 : ℕ) : ℝ≥0) * w n))
        atTop (𝓝 t)) :
    ∀ᶠ n : ℕ in atTop,
      Set.InjOn (fun t => idx t n) (F : Set ℝ≥0) := by
  exact avram_p2_a_zero_rate_finite_selected_cells_eventually_injective
    F idx (by
      intro u hu v hv hne
      exact avram_p2_a_zero_rate_selected_cell_indices_eventually_distinct
        u v hne (idx u) (idx v) w (hright u hu) (hright v hv))
