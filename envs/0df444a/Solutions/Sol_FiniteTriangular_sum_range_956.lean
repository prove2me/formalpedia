-- Prove2me | solution 1 for FiniteTriangular.sum_range_956
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:01:00.382474+00:00
-- url     : https://prove2.me/submissions/454f4563-4b22-491c-a7fe-7cb4aa7ac0e0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 956, k = 456490 := by
  rw [sum_range_id]
