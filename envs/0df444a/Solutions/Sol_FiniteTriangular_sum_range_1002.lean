-- Prove2me | solution 1 for FiniteTriangular.sum_range_1002
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:40:49.391984+00:00
-- url     : https://prove2.me/submissions/6916b651-4a4a-4abf-902c-64cd552c28ad

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1002, k = 501501 := by
  rw [sum_range_id]
