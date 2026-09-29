-- Prove2me | solution 1 for FiniteTriangular.sum_range_304
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:20:08.719411+00:00
-- url     : https://prove2.me/submissions/ce491aa4-c60d-4c4c-90cb-1ada746b3c3e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 304, k = 46056 := by
  rw [sum_range_id]
