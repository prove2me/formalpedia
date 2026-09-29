-- Prove2me | solution 1 for FiniteTriangular.sum_range_210
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:51:41.919703+00:00
-- url     : https://prove2.me/submissions/93b7e387-a9a1-42e1-aa37-063dd7e0434c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 210, k = 21945 := by
  rw [sum_range_id]
