-- Prove2me | solution 1 for FiniteTriangular.sum_range_459
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:12:03.486926+00:00
-- url     : https://prove2.me/submissions/af45cf06-d737-4a1f-bf48-63d00f0a2df6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 459, k = 105111 := by
  rw [sum_range_id]
