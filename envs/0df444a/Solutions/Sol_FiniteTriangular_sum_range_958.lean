-- Prove2me | solution 1 for FiniteTriangular.sum_range_958
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:01:02.433032+00:00
-- url     : https://prove2.me/submissions/68dd46a2-9f77-4e42-9a92-f5db48441587

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 958, k = 458403 := by
  rw [sum_range_id]
