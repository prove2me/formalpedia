-- Prove2me | solution 1 for FiniteTriangular.sum_range_891
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:47:07.32223+00:00
-- url     : https://prove2.me/submissions/dc2c0c97-91cd-49cf-864f-d94d5c46d16b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 891, k = 396495 := by
  rw [sum_range_id]
