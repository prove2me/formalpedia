-- Prove2me | solution 1 for FiniteTriangular.sum_range_236
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:57:45.303102+00:00
-- url     : https://prove2.me/submissions/88a04a9f-e031-4d11-9e4b-f5c5a8d1bafa

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 236, k = 27730 := by
  rw [sum_range_id]
