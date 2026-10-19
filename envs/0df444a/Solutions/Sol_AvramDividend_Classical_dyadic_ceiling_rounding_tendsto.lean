-- Prove2me | solution 1 for AvramDividend.Classical.dyadic_ceiling_rounding_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:13:46.639748+00:00
-- url     : https://prove2.me/submissions/383c6eaf-527a-44a9-98c9-16b3eff86754

import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped NNReal ENNReal

theorem solution
    (t : ℝ≥0) :
    Tendsto
      (fun n : ℕ =>
        (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ) / (2 : ℝ) ^ n)
      atTop (𝓝 (t : ℝ)) := by
  have h0 : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hup : Tendsto (fun n : ℕ => (t : ℝ) + ((1 : ℝ) / 2) ^ n) atTop (𝓝 (t : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (t : ℝ))).add h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup ?_ ?_
  · intro n
    have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    show (t : ℝ) ≤ _
    rw [le_div_iff₀ hp]
    exact Nat.le_ceil _
  · intro n
    have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    show _ ≤ (t : ℝ) + ((1 : ℝ) / 2) ^ n
    rw [div_le_iff₀ hp]
    have h1 := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (t : ℝ) * (2 : ℝ) ^ n by positivity)).le
    have h2 : ((t : ℝ) + ((1 : ℝ) / 2) ^ n) * (2 : ℝ) ^ n = (t : ℝ) * (2 : ℝ) ^ n + 1 := by
      rw [add_mul, ← mul_pow]; norm_num
    rw [h2]; exact h1
