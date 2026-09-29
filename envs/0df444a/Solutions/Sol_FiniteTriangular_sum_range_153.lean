-- Prove2me | solution 1 for FiniteTriangular.sum_range_153
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:17:46.699671+00:00
-- url     : https://prove2.me/submissions/1e40556d-e18a-491a-80b3-160012fad044

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 153, k = 11628 := by
  rw [sum_range_id]
