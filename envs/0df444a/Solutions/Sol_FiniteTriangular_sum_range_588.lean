-- Prove2me | solution 1 for FiniteTriangular.sum_range_588
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:41:34.367163+00:00
-- url     : https://prove2.me/submissions/a81db18f-207f-46a8-ac78-3cfc28ac975a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 588, k = 172578 := by
  rw [sum_range_id]
