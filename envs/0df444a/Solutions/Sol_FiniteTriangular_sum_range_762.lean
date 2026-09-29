-- Prove2me | solution 1 for FiniteTriangular.sum_range_762
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:19:49.095917+00:00
-- url     : https://prove2.me/submissions/fa6e030f-a074-4471-929a-7378a0f4ffe3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 762, k = 289941 := by
  rw [sum_range_id]
