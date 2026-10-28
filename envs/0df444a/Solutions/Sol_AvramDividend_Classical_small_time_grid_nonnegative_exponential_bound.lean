-- Prove2me | solution 1 for AvramDividend.Classical.small_time_grid_nonnegative_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:52:27.424987+00:00
-- url     : https://prove2.me/submissions/7cc2a264-92f7-4631-bbde-d4c76c12e3d9

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
open Real
theorem solution
    (p : ℝ) (n : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) ^ n ≤ Real.exp (-((n : ℝ) * p)) := by 
  have h1 : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  calc (1 - p) ^ n ≤ Real.exp (-p) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    _ = Real.exp (-((n : ℝ) * p)) := by rw [← Real.exp_nat_mul]; ring_nf
