-- Prove2me | solution 1 for FiniteTriangular.sum_range_433
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:57:34.368823+00:00
-- url     : https://prove2.me/submissions/6bcd9d9a-5f53-4c7d-ae7f-d233a656fc9a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 433, k = 93528 := by
  rw [sum_range_id]
