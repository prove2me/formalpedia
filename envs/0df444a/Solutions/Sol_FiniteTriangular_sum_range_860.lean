-- Prove2me | solution 1 for FiniteTriangular.sum_range_860
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:40:11.439675+00:00
-- url     : https://prove2.me/submissions/f8d7ef84-96e2-492b-b862-f52230aaab7a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 860, k = 369370 := by
  rw [sum_range_id]
