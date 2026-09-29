-- Prove2me | solution 1 for FiniteTriangular.sum_range_1007
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:40:52.647982+00:00
-- url     : https://prove2.me/submissions/d74474e0-3ce9-4aaa-a929-29077eefc09d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1007, k = 506521 := by
  rw [sum_range_id]
