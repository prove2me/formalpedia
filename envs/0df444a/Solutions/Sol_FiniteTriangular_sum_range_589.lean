-- Prove2me | solution 1 for FiniteTriangular.sum_range_589
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:41:35.021811+00:00
-- url     : https://prove2.me/submissions/23c0b22e-eadb-42e9-82a8-2a8a67a2a69f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 589, k = 173166 := by
  rw [sum_range_id]
