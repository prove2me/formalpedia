-- Prove2me | solution 1 for FiniteTriangular.sum_range_165
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:20:37.459076+00:00
-- url     : https://prove2.me/submissions/750ee0c2-b872-43f5-8c74-4cfd963c996b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 165, k = 13530 := by
  rw [sum_range_id]
