-- Prove2me | solution 1 for FiniteTriangular.sum_range_1092
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:24:00.21619+00:00
-- url     : https://prove2.me/submissions/e94081c5-2f8b-4dfb-8638-f0fb2f2c3ebf

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1092, k = 595686 := by
  rw [sum_range_id]
