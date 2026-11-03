-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_path_dense_grid_first_downcrossing_recovers_jump_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:06:09.691119+00:00
-- url     : https://prove2.me/submissions/b1126916-59c1-4d52-9751-44b12cf303a3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_path_dense_grid_any_prior_start_exact_downcrossing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Recover an exact separated downcrossing using the stronger all-prior-grid-start theorem. -/
theorem solution
    (Y : ℝ≥0 → ℝ)
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (s t b : ℝ≥0) (a : ℝ) (hst : s < t) (htb : t < b)
    (hL : ∀ u ∈ Ioo s t, a < Y u)
    (hR : ∀ u ∈ Ico t b, Y u < a) :
    ∃ m : ℕ, grid m ∈ Ioo s t ∧
      (⨅ n : ℕ,
        {Z : ℝ≥0 → ℝ | grid m < grid n ∧ Z (grid n) < a}.piecewise
          (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y) =
      (t : ℝ≥0∞) := by
  obtain ⟨v, ⟨m, rfl⟩, hm⟩ := hdense.exists_between hst
  refine ⟨m, hm, ?_⟩
  exact avram_wave7_01_path_dense_grid_any_prior_start_exact_downcrossing
    Y grid hdense s t b a hst htb hL hR m hm
