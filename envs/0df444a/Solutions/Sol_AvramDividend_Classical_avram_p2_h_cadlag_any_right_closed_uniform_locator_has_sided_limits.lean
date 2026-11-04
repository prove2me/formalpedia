-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_any_right_closed_uniform_locator_has_sided_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:14:25.500806+00:00
-- url     : https://prove2.me/submissions/cca3464f-2dad-4c09-800a-c08071a02092

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_original_grid_adjacent_duration
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_vanishing_width_halfopen_endpoints

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Every choice of the right-closed source grid locator gives the
correct one-sided endpoint limits, by the exact NNReal cell width. -/
theorem solution
    (T u : ℝ≥0) (j : ℕ → ℕ)
    (hj : ∀ n : ℕ,
      (j n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
        u ≤ (((j n + 1 : ℕ) : ℝ≥0) *
          (T / ((n : ℝ≥0) + 1)))) :
    Tendsto (fun n : ℕ =>
      (j n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))
      atTop (𝓝[<] u) ∧
    Tendsto (fun n : ℕ =>
      (((j n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
      atTop (nhdsWithin u (Ici u)) := by
  let a : ℕ → ℝ≥0 :=
    fun n => (j n : ℝ≥0) * (T / ((n : ℝ≥0) + 1))
  let b : ℕ → ℝ≥0 :=
    fun n => (((j n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))
  have hab : ∀ n, a n < u ∧ u ≤ b n := by
    intro n
    exact hj n
  have heq : (fun n => b n - a n) =
      (fun n : ℕ => T / ((n : ℝ≥0) + 1)) := by
    funext n
    exact avram_p2_34dbea70_uniform_original_grid_adjacent_duration
      T n (j n)
  have hwidth : Tendsto (fun n => b n - a n)
      atTop (𝓝 (0 : ℝ≥0)) := by
    rw [heq]
    exact avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero T
  exact avram_p2_34dbea70_vanishing_width_halfopen_endpoints
    u a b hab hwidth
