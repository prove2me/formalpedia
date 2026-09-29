-- Prove2me | solution 1 for FiniteTriangular.sum_range_1009
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:42:26.808977+00:00
-- url     : https://prove2.me/submissions/6f81f746-777a-47c3-96b8-0b02f4891a73

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1009, k = 508536 := by
  rw [sum_range_id]
