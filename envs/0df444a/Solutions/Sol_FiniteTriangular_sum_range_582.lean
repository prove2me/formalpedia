-- Prove2me | solution 1 for FiniteTriangular.sum_range_582
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:39:49.944895+00:00
-- url     : https://prove2.me/submissions/7f493c36-d8f5-4ae9-9043-ce60f2159280

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 582, k = 169071 := by
  rw [sum_range_id]
