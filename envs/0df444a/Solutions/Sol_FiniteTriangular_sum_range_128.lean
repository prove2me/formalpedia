-- Prove2me | solution 1 for FiniteTriangular.sum_range_128
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:13:24.853243+00:00
-- url     : https://prove2.me/submissions/1b62f8b0-b43f-4d02-ba8d-fc25c7e1ab06

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 128, k = 8128 := by
  rw [sum_range_id]
