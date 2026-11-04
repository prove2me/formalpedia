-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_uniform_source_jump_cells_sided_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:35:50.415711+00:00
-- url     : https://prove2.me/submissions/d1f172f3-0329-47eb-b0ff-e405323edee8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_halfopen_cell_locator
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_vanishing_width_halfopen_endpoints

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Choose actual half-open uniform cells around a positive source time and
prove their strictly-left and weak-right endpoint limits. -/
theorem solution (T u : ℝ≥0) (hT : 0 < T) (hu : 0 < u) (huT : u ≤ T) :
    ∃ i : ℕ → ℕ,
      (∀ n, i n ≤ n ∧
        (i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
        u ≤ ((i n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∧
      Tendsto (fun n => (i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))
        atTop (𝓝[<] u) ∧
      Tendsto (fun n => ((i n + 1 : ℕ) : ℝ≥0) *
        (T / ((n : ℝ≥0) + 1))) atTop (nhdsWithin u (Ici u)) := by
  classical
  have hloc (n : ℕ) : ∃ j : ℕ, j ≤ n ∧
      (j : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
      u ≤ ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) :=
    avram_p2_34dbea70_uniform_halfopen_cell_locator T u hT hu huT n
  let i : ℕ → ℕ := fun n => Classical.choose (hloc n)
  have hi (n : ℕ) : i n ≤ n ∧
      (i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
      u ≤ ((i n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) :=
    Classical.choose_spec (hloc n)
  let d : ℕ → ℝ≥0 := fun n => T / ((n : ℝ≥0) + 1)
  let a : ℕ → ℝ≥0 := fun n => (i n : ℝ≥0) * d n
  let b : ℕ → ℝ≥0 := fun n => ((i n + 1 : ℕ) : ℝ≥0) * d n
  have hab : ∀ n, a n < u ∧ u ≤ b n := by
    intro n
    exact ⟨(hi n).2.1, (hi n).2.2⟩
  have hstep (n : ℕ) : b n = a n + d n := by
    dsimp [a, b, d]
    push_cast
    ring
  have hwidth_eq (n : ℕ) : b n - a n = d n := by
    rw [hstep]
    simp
  have hwidth : Tendsto (fun n => b n - a n) atTop (𝓝 (0 : ℝ≥0)) := by
    simpa only [hwidth_eq, d] using
      avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero T
  obtain ⟨ha, hb⟩ :=
    avram_p2_34dbea70_vanishing_width_halfopen_endpoints u a b hab hwidth
  refine ⟨i, fun n => hi n, ?_, ?_⟩
  · exact ha
  · exact hb
