-- Prove2me | solution 1 for FiniteTriangular.sum_range_1044
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:13:18.721183+00:00
-- url     : https://prove2.me/submissions/0ffc69ab-685a-46c8-9e9b-f75c7d46b853

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1044, k = 544446 := by
  rw [sum_range_id]
