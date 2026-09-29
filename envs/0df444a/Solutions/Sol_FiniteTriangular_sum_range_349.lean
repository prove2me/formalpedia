-- Prove2me | solution 1 for FiniteTriangular.sum_range_349
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:37:51.532023+00:00
-- url     : https://prove2.me/submissions/f3054e5d-7e94-4be5-9cd1-606d9047ab5d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 349, k = 60726 := by
  rw [sum_range_id]
