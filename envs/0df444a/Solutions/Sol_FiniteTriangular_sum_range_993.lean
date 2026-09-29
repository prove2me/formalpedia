-- Prove2me | solution 1 for FiniteTriangular.sum_range_993
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:38:47.181979+00:00
-- url     : https://prove2.me/submissions/eeeb67cf-9d6a-41fd-bc58-2ba0ff0948c7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 993, k = 492528 := by
  rw [sum_range_id]
