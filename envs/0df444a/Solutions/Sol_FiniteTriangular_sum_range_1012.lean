-- Prove2me | solution 1 for FiniteTriangular.sum_range_1012
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:42:28.802976+00:00
-- url     : https://prove2.me/submissions/b5f91a5c-1379-4561-9b26-d4845c986738

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1012, k = 511566 := by
  rw [sum_range_id]
