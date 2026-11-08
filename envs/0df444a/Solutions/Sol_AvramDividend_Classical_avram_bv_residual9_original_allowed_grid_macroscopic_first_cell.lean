-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_original_allowed_grid_macroscopic_first_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:00:42.8245+00:00
-- url     : https://prove2.me/submissions/5961424b-f47b-45a3-aafc-573d0ba87176

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_monotone_grid_nonuniform_counterexample
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact admissible grid axioms permit a macroscopic first cell
    at every index, so they cannot force mesh-size convergence to zero. -/
theorem solution
    (T : ℝ) (hT : 0 < T) :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧
        ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n, T / 2 ≤ (u n 1 : ℝ) - (u n 0 : ℝ)) := by
  obtain ⟨u, hgrid, hmono, hlast, _⟩ :=
    avram_bv_residual9_monotone_grid_nonuniform_counterexample T hT
  refine ⟨u, hgrid, hmono, ?_⟩
  intro n
  have hwidth :
      (u n 1 : ℝ) - (u n 0 : ℝ) =
        T - T / ((n : ℝ) + 2) := by
    simpa only [(hgrid n).1, hlast n, NNReal.coe_zero, sub_zero] using
      (hgrid n).2
  rw [hwidth]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith
  have hfrac : T / ((n : ℝ) + 2) ≤ T / 2 := by
    exact div_le_div_of_nonneg_left (le_of_lt hT) (by norm_num) hden
  linarith
