-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb25_uniform_cell_source_sum_as_restricted_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:27:34.247255+00:00
-- url     : https://prove2.me/submissions/6a206787-dbfd-44a4-97d3-6d0a53fa6670

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bva21_uniform_frozen_grid_sum_as_real_floor_integral
import Theorems.Thm_AvramDividend_Classical_avram_bva21_uniform_floor_step_integral_restrict_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) (n : ℕ) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ k i, (u k i : ℝ) =
       T * (i : ℝ) / ((k : ℝ) + 2))
    (c : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1),
       c i * ((u n (i + 1) : ℝ) - (u n i : ℝ))) =
    ∫ r in Set.Icc (0 : ℝ) T,
      (if 0 ≤ r ∧ r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
       then c ⌊(r / T) * ((n : ℝ) + 2)⌋₊ else 0) := by
  have hWidth (i : ℕ) :
      (u n (i + 1) : ℝ) - (u n i : ℝ) =
        T / ((n : ℝ) + 2) := by
    rw [huniform n (i + 1), huniform n i]
    push_cast
    ring
  calc
    (∑ i ∈ Finset.range (n + 1),
        c i * ((u n (i + 1) : ℝ) - (u n i : ℝ))) =
      ∑ i ∈ Finset.range (n + 1),
        (T / ((n : ℝ) + 2)) * c i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hWidth i]
          ring
    _ = ∫ r : ℝ,
      (if 0 ≤ r ∧ r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
       then c ⌊(r / T) * ((n : ℝ) + 2)⌋₊ else 0) :=
      avram_bva21_uniform_frozen_grid_sum_as_real_floor_integral T hT n c
    _ = ∫ r in Set.Icc (0 : ℝ) T,
      (if 0 ≤ r ∧ r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
       then c ⌊(r / T) * ((n : ℝ) + 2)⌋₊ else 0) :=
      avram_bva21_uniform_floor_step_integral_restrict_horizon T hT n c
