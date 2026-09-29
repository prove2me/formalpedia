-- Prove2me | solution 1 for FiniteTriangular.sum_range_192
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:45:21.189973+00:00
-- url     : https://prove2.me/submissions/d6c8c7be-cb25-4224-8360-455d48822d4b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 192, k = 18336 := by
  rw [sum_range_id]
