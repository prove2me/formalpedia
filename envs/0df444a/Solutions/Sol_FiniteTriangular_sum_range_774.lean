-- Prove2me | solution 1 for FiniteTriangular.sum_range_774
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:21:39.756183+00:00
-- url     : https://prove2.me/submissions/e7dc8dac-b54d-4419-b32e-ce516da5cbcb

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 774, k = 299151 := by
  rw [sum_range_id]
