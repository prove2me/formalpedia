-- Prove2me | solution 1 for FiniteTriangular.sum_range_1005
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:40:51.333986+00:00
-- url     : https://prove2.me/submissions/39123053-e655-46e1-887a-73507661e97e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1005, k = 504510 := by
  rw [sum_range_id]
