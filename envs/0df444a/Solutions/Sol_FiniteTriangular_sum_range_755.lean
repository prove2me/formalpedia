-- Prove2me | solution 1 for FiniteTriangular.sum_range_755
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:18:12.359141+00:00
-- url     : https://prove2.me/submissions/5be04eb3-7559-49f1-bb56-2948d2ae1e83

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 755, k = 284635 := by
  rw [sum_range_id]
