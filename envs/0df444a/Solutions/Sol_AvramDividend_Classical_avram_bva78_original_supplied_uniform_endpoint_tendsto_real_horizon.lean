-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva78_original_supplied_uniform_endpoint_tendsto_real_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:06:23.587837+00:00
-- url     : https://prove2.me/submissions/5067456b-d485-40ee-b0db-231e678340a3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    Tendsto (fun n : ℕ => (u n (n + 1) : ℝ)) atTop (𝓝 T) := by
  have hlim :=
    (avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon T hT).2
  have hEq :
      (fun n : ℕ => (u n (n + 1) : ℝ)) =
        (fun n : ℕ => T - T / ((n : ℝ) + 2)) := by
    funext n
    have hd : (n : ℝ) + 2 ≠ 0 := by positivity
    rw [huniform n (n + 1)]
    push_cast
    field_simp
    ring
  rw [hEq]
  exact hlim
