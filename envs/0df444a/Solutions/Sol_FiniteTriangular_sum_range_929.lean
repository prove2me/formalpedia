-- Prove2me | solution 1 for FiniteTriangular.sum_range_929
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:55:31.915907+00:00
-- url     : https://prove2.me/submissions/a24b3af2-2c9d-43b4-b58c-128d3d1c1b11

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 929, k = 431056 := by
  rw [sum_range_id]
