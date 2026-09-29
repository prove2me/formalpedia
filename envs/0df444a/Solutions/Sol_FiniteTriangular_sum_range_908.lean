-- Prove2me | solution 1 for FiniteTriangular.sum_range_908
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:50:22.411465+00:00
-- url     : https://prove2.me/submissions/e95392b5-9808-4b2b-9a9a-6b6eb584e2bb

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 908, k = 411778 := by
  rw [sum_range_id]
