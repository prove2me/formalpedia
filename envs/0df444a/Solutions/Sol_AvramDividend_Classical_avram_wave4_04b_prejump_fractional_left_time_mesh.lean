-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_prejump_fractional_left_time_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:19:27.911469+00:00
-- url     : https://prove2.me/submissions/c88cd14d-baac-44ab-9082-16d6a7b3dac7

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

/-- The source-free mesh approaches each positive time strictly from the left. -/
theorem solution :
    (∀ n : ℕ, Measurable
      (fun t : ℝ≥0 => t - t * (1 / 2 : ℝ≥0) ^ (n + 1))) ∧
    (∀ t : ℝ≥0, Tendsto
      (fun n : ℕ => t - t * (1 / 2 : ℝ≥0) ^ (n + 1))
      atTop (𝓝 t)) ∧
    (∀ t : ℝ≥0, 0 < t → ∀ n : ℕ,
      t - t * (1 / 2 : ℝ≥0) ^ (n + 1) < t) := by
  let q : ℕ → ℝ≥0 := fun n => (1 / 2 : ℝ≥0) ^ (n + 1)
  have hq : Tendsto q atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ≥0) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact hp.comp (tendsto_add_atTop_nat 1)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change Measurable (fun t : ℝ≥0 => t - t * q n)
    exact measurable_id.sub (measurable_id.mul_const (q n))
  · intro t
    change Tendsto (fun n : ℕ => t - t * q n) atTop (𝓝 t)
    have hsmall : Tendsto (fun n : ℕ => t * q n) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hq
    convert tendsto_const_nhds.sub hsmall using 1 <;> simp
  · intro t ht n
    change t - t * q n < t
    have hpos : 0 < q n := by dsimp [q]; positivity
    exact tsub_lt_self ht (mul_pos ht hpos)
