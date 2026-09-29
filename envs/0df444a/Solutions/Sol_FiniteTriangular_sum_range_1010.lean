-- Prove2me | solution 1 for FiniteTriangular.sum_range_1010
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:42:27.434672+00:00
-- url     : https://prove2.me/submissions/5020e90c-2f17-4a8a-ae82-8ae33cc9e535

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1010, k = 509545 := by
  rw [sum_range_id]
