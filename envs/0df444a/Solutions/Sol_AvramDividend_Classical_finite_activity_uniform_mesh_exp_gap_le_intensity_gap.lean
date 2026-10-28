-- Prove2me | solution 1 for AvramDividend.Classical.finite_activity_uniform_mesh_exp_gap_le_intensity_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:27:40.525481+00:00
-- url     : https://prove2.me/submissions/1818ffd3-eb71-4455-be20-9f10b0ad65bf

import Theorems.Thm_AvramDividend_Classical_exponential_decay_difference_le_interval_length
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- The grid size cancels from the exponentially discounted finite-activity gap. -/
theorem solution
    (a b T : ℝ) (N : ℕ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hT : 0 ≤ T) (hN : 0 < N) :
    (N : ℝ) *
      (Real.exp (-((T / (N : ℝ)) * a)) -
        Real.exp (-((T / (N : ℝ)) * b))) ≤ T * (b - a) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdiv : 0 ≤ T / (N : ℝ) :=
    div_nonneg hT (le_of_lt hNreal)
  have hargnonneg : 0 ≤ (T / (N : ℝ)) * a := mul_nonneg hdiv ha
  have hargle :
      (T / (N : ℝ)) * a ≤ (T / (N : ℝ)) * b :=
    mul_le_mul_of_nonneg_left hab hdiv
  have hbase :=
    exponential_decay_difference_le_interval_length
      ((T / (N : ℝ)) * a) ((T / (N : ℝ)) * b) hargnonneg hargle
  have hbound :=
    mul_le_mul_of_nonneg_left hbase (le_of_lt hNreal)
  calc
    (N : ℝ) *
        (Real.exp (-((T / (N : ℝ)) * a)) -
          Real.exp (-((T / (N : ℝ)) * b))) ≤
        (N : ℝ) *
          (((T / (N : ℝ)) * b) - ((T / (N : ℝ)) * a)) := hbound
    _ = T * (b - a) := by
      have hNe : (N : ℝ) ≠ 0 := ne_of_gt hNreal
      field_simp [hNe]
      <;> ring
