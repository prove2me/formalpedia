-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB279_fourth_power_gaussian_mesh_inverse_linear_scaling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:01:14.137475+00:00
-- url     : https://prove2.me/submissions/8efb42c6-be55-44a5-a51c-6a7d9e101461

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- On the fourth-power grid, inverse-cube width times square-root cell length yields inverse refinement. -/
theorem solution (n m : ℕ) (hm : 0 < m) :
    ((n * m ^ 4 : ℕ) : ℝ) * (1 / ((m : ℝ) ^ 3)) *
      Real.sqrt (1 / ((m : ℝ) ^ 4)) = (n : ℝ) / (m : ℝ) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hne : (m : ℝ) ≠ 0 := ne_of_gt hmr
  have hsqrt : Real.sqrt (1 / ((m : ℝ) ^ 4)) = 1 / ((m : ℝ) ^ 2) := by
    calc
      Real.sqrt (1 / ((m : ℝ) ^ 4)) =
          Real.sqrt ((1 / ((m : ℝ) ^ 2)) ^ 2) := by
            congr 1
            field_simp <;> ring
      _ = |1 / ((m : ℝ) ^ 2)| := Real.sqrt_sq_eq_abs _
      _ = 1 / ((m : ℝ) ^ 2) := abs_of_pos (by positivity)
  rw [hsqrt]
  push_cast
  field_simp <;> ring

-- Rebased proof source for the current Prove2Me checker; the mathematical proof is unchanged.
