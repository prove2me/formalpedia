-- Prove2me | solution 1 for FiniteTriangular.sum_range_505
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:22:19.595899+00:00
-- url     : https://prove2.me/submissions/aa55131e-b3e9-448a-9a31-5786fd1ff302

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 505, k = 127260 := by
  rw [sum_range_id]
