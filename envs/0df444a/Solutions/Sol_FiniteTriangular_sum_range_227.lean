-- Prove2me | solution 1 for FiniteTriangular.sum_range_227
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:55:12.526044+00:00
-- url     : https://prove2.me/submissions/6f40163e-7d80-44b1-90e4-d1674285fe3c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 227, k = 25651 := by
  rw [sum_range_id]
