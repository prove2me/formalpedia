-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_uniform_floor_sample_mem_halfopen_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:20:00.478628+00:00
-- url     : https://prove2.me/submissions/a6df4dc0-4bb1-4ecb-8d73-91897fe38ad7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
noncomputable section

/-- The physical floor sample selects the unique uniform half-open grid cell. -/
theorem solution
    (T : ℝ) (hT : 0 < T) (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    let k : ℕ := ⌊(r / T) * ((n : ℝ) + 2)⌋₊
    r ∈ Set.Ico
      (T * (k : ℝ) / ((n : ℝ) + 2))
      (T * ((k : ℝ) + 1) / ((n : ℝ) + 2)) := by
  intro k
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have ha : 0 ≤ (r / T) * ((n : ℝ) + 2) :=
    mul_nonneg (div_nonneg hr hT.le) hden.le
  have hf : (k : ℝ) ≤ (r / T) * ((n : ℝ) + 2) := by
    dsimp [k]
    exact Nat.floor_le ha
  have hf' : (r / T) * ((n : ℝ) + 2) < (k : ℝ) + 1 := by
    dsimp [k]
    exact Nat.lt_floor_add_one _
  constructor
  · apply (div_le_iff₀ hden).2
    calc
      T * (k : ℝ) ≤ T * ((r / T) * ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hf hT.le
      _ = r * ((n : ℝ) + 2) := by
        field_simp [ne_of_gt hT]
  · apply (lt_div_iff₀ hden).2
    calc
      r * ((n : ℝ) + 2) = T * ((r / T) * ((n : ℝ) + 2)) := by
        field_simp [ne_of_gt hT]
      _ < T * ((k : ℝ) + 1) := mul_lt_mul_of_pos_left hf' hT
