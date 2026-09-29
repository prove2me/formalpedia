-- Prove2me | solution 1 for FiniteTriangular.sum_range_207
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:49:30.708393+00:00
-- url     : https://prove2.me/submissions/747c5689-2402-46d9-9b73-971024f655ee

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 207, k = 21321 := by
  rw [sum_range_id]
