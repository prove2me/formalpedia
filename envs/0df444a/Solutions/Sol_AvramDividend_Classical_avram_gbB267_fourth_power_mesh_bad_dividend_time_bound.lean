-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB267_fourth_power_mesh_bad_dividend_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:46:13.899364+00:00
-- url     : https://prove2.me/submissions/8d835003-db01-4190-b4c4-464f679c8600

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB257_monotone_grid_large_dividend_cell_count_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset AvramDividend.Classical
noncomputable section

/-- The fourth-power grid with cubic threshold yields a linear inverse-refinement bad-cell estimate. -/
theorem solution
    (d : ℕ → ℝ) (hd : Monotone d)
    (m n : ℕ) (hm : 0 < m) :
    (((Finset.range (n * m ^ 4)).filter
      (fun i => 1 / ((m : ℝ) ^ 3) < d (i + 1) - d i)).card : ℝ) *
      (1 / ((m : ℝ) ^ 4)) ≤
    (d (n * m ^ 4) - d 0) / (m : ℝ) := by
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hEps : (0 : ℝ) < 1 / ((m : ℝ) ^ 3) := by positivity
  have h :=
    avram_gbB257_monotone_grid_large_dividend_cell_count_bound
      d hd (1 / ((m : ℝ) ^ 3)) hEps (n * m ^ 4)
  calc
    (((Finset.range (n * m ^ 4)).filter
      (fun i => 1 / ((m : ℝ) ^ 3) < d (i + 1) - d i)).card : ℝ) *
        (1 / ((m : ℝ) ^ 4)) =
      (((Finset.range (n * m ^ 4)).filter
        (fun i => 1 / ((m : ℝ) ^ 3) < d (i + 1) - d i)).card : ℝ) *
        (1 / ((m : ℝ) ^ 3)) * (1 / (m : ℝ)) := by
          field_simp
    _ ≤ (d (n * m ^ 4) - d 0) * (1 / (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_right h (by positivity)
    _ = (d (n * m ^ 4) - d 0) / (m : ℝ) := by ring
