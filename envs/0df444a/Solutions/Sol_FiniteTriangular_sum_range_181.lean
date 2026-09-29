-- Prove2me | solution 1 for FiniteTriangular.sum_range_181
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:24:28.262906+00:00
-- url     : https://prove2.me/submissions/ee92bba6-2ff3-486b-aad7-0f80b6774866

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 181, k = 16290 := by
  rw [sum_range_id]
