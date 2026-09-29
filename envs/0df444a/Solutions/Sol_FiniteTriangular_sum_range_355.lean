-- Prove2me | solution 1 for FiniteTriangular.sum_range_355
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:39:27.697793+00:00
-- url     : https://prove2.me/submissions/561b0042-1e39-4d53-82d3-b770e4aed016

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 355, k = 62835 := by
  rw [sum_range_id]
