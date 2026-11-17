-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_quadratic_uniform_cell_collision_budget_vanishes_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:15:25.892284+00:00
-- url     : https://prove2.me/submissions/dfb38d0e-0051-42cd-b86b-fc1ec7e19c19

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
noncomputable section
theorem solution (a : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * ((a / (n : ℝ)) ^ 2 / 2))
      atTop (𝓝 (0 : ℝ)) := by
  have heq : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * ((a / (n : ℝ)) ^ 2 / 2) =
        (a ^ 2 / 2) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp [hn0]
    <;> ring
  have ht : Tendsto (fun n : ℕ => (a ^ 2 / 2) / (n : ℝ))
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  exact ht.congr' (heq.mono (fun n hn => hn.symm))
