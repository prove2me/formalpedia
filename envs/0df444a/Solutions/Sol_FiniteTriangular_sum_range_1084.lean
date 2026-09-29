-- Prove2me | solution 1 for FiniteTriangular.sum_range_1084
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:22:27.391511+00:00
-- url     : https://prove2.me/submissions/d8cfe72a-78ba-4388-9945-bfd44c50ba0a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1084, k = 586986 := by
  rw [sum_range_id]
