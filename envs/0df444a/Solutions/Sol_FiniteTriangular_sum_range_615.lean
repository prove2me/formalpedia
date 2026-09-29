-- Prove2me | solution 1 for FiniteTriangular.sum_range_615
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:46:45.413228+00:00
-- url     : https://prove2.me/submissions/529a24d6-1779-46a5-8358-9d9089c60731

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 615, k = 188805 := by
  rw [sum_range_id]
