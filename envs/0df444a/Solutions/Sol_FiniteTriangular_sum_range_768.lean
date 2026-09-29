-- Prove2me | solution 1 for FiniteTriangular.sum_range_768
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:19:53.194878+00:00
-- url     : https://prove2.me/submissions/9243b108-042b-4dcb-8b14-d65efc6b6fee

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 768, k = 294528 := by
  rw [sum_range_id]
