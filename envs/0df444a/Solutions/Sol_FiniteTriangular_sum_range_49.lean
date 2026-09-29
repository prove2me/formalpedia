-- Prove2me | solution 1 for FiniteTriangular.sum_range_49
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:17:23.610984+00:00
-- url     : https://prove2.me/submissions/9ce0fd79-3f46-42b4-9fed-7bf7461c215a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 49, k = 1176 := by
  decide
