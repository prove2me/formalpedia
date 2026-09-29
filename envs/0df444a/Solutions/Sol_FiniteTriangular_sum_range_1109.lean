-- Prove2me | solution 1 for FiniteTriangular.sum_range_1109
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:27:33.099397+00:00
-- url     : https://prove2.me/submissions/93dca2cc-8eee-453d-ad86-f516fe7cd697

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1109, k = 614386 := by
  rw [sum_range_id]
