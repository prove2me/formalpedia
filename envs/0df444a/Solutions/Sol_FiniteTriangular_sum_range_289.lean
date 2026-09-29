-- Prove2me | solution 1 for FiniteTriangular.sum_range_289
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:18:17.437066+00:00
-- url     : https://prove2.me/submissions/489a8ec5-507a-4a74-b22d-d5c501e17586

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 289, k = 41616 := by
  rw [sum_range_id]
