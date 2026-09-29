-- Prove2me | solution 1 for FiniteTriangular.sum_range_747
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:16:31.766569+00:00
-- url     : https://prove2.me/submissions/72e5d60b-697e-470f-a25c-85ef9816dd12

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 747, k = 278631 := by
  rw [sum_range_id]
