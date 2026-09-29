-- Prove2me | solution 1 for FiniteTriangular.sum_range_424
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:54:06.526242+00:00
-- url     : https://prove2.me/submissions/bb81e1e7-e0ac-4b20-8c03-38d0081d007c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 424, k = 89676 := by
  rw [sum_range_id]
