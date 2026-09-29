-- Prove2me | solution 1 for FiniteTriangular.sum_range_833
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:35:19.369397+00:00
-- url     : https://prove2.me/submissions/cb274097-7cd7-42e4-ac12-060145829c0e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 833, k = 346528 := by
  rw [sum_range_id]
