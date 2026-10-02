-- Prove2me | solution 1 for ChatterjeeSamuelson.UniformEfficiency.total_profit_sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-01T19:01:39.871982+00:00
-- url     : https://prove2.me/submissions/ae80acd2-4231-45ca-a210-ceae99757597

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

theorem solution (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hv : 0 < vbar) :
    vbar / 48 * (2 - k) ^ 2 * (1 + k) + vbar / 48 * (1 + k) ^ 2 * (2 - k) =
      vbar / 16 * (1 + k) * (2 - k) := by
  ring
