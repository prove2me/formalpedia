-- Prove2me | solution 1 for FiniteTriangular.sum_range_619
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:48:19.720645+00:00
-- url     : https://prove2.me/submissions/405786c7-0fe9-43cf-a25b-68524070c429

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 619, k = 191271 := by
  rw [sum_range_id]
