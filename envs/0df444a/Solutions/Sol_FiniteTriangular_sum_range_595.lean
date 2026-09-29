-- Prove2me | solution 1 for FiniteTriangular.sum_range_595
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:43:09.528361+00:00
-- url     : https://prove2.me/submissions/dedb6244-f6ed-4843-8440-049fbfd76255

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 595, k = 176715 := by
  rw [sum_range_id]
