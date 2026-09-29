-- Prove2me | solution 1 for FiniteTriangular.sum_range_997
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:38:49.723601+00:00
-- url     : https://prove2.me/submissions/4e387dc9-40a8-4747-92e5-96ba1408e2c8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 997, k = 496506 := by
  rw [sum_range_id]
