-- Prove2me | solution 1 for FiniteTriangular.sum_range_423
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:54:05.91087+00:00
-- url     : https://prove2.me/submissions/9b7ffa26-79aa-41bf-b59d-5b0dad9e99f3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 423, k = 89253 := by
  rw [sum_range_id]
