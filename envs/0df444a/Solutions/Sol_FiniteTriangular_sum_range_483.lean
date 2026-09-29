-- Prove2me | solution 1 for FiniteTriangular.sum_range_483
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:17:21.800875+00:00
-- url     : https://prove2.me/submissions/0d474503-e429-4575-b6a5-6fd570010074

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 483, k = 116403 := by
  rw [sum_range_id]
