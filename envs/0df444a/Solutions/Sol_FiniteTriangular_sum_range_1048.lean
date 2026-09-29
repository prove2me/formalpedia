-- Prove2me | solution 1 for FiniteTriangular.sum_range_1048
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:13:21.191966+00:00
-- url     : https://prove2.me/submissions/415b9382-0cbc-47dd-80e7-73f7643d2278

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1048, k = 548628 := by
  rw [sum_range_id]
