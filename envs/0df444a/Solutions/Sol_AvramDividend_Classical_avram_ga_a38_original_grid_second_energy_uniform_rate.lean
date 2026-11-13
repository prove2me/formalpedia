-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a38_original_grid_second_energy_uniform_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:17:03.37427+00:00
-- url     : https://prove2.me/submissions/2db13730-144e-4033-b57c-29ce3f540863

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- The unnormalised Gaussian variance energy over a uniform physical mesh is bounded by its horizon.
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (n m : ℕ) (σ : ℝ) :
    (m : ℝ) * (((n : ℝ) / ((m : ℝ) + 1)) * σ ^ 2) ≤
      (n : ℝ) * σ ^ 2 := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hmn : (m : ℝ) * ((n : ℝ) / ((m : ℝ) + 1)) ≤
      (n : ℝ) := by
    calc
      (m : ℝ) * ((n : ℝ) / ((m : ℝ) + 1)) =
        (m : ℝ) * (n : ℝ) / ((m : ℝ) + 1) := by ring
      _ ≤ (n : ℝ) := by
        apply (div_le_iff₀ hm).2
        nlinarith
  have hs : 0 ≤ σ ^ 2 := sq_nonneg σ
  have hh := mul_le_mul_of_nonneg_right hmn hs
  nlinarith
