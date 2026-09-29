-- Prove2me | solution 1 for FiniteTriangular.sum_range_725
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:10:59.87393+00:00
-- url     : https://prove2.me/submissions/3d502517-3100-4570-b3dc-1cb81bdf9b7a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 725, k = 262450 := by
  rw [sum_range_id]
