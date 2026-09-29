-- Prove2me | solution 1 for FiniteTriangular.sum_range_348
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:37:50.799808+00:00
-- url     : https://prove2.me/submissions/ef53c65f-306d-4d8c-b8a3-23ce29e36e3b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 348, k = 60378 := by
  rw [sum_range_id]
