-- Prove2me | solution 1 for FiniteTriangular.sum_range_531
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:27:29.409285+00:00
-- url     : https://prove2.me/submissions/d384ab48-962c-46a4-b6ce-6d41fa32d6d3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 531, k = 140715 := by
  rw [sum_range_id]
