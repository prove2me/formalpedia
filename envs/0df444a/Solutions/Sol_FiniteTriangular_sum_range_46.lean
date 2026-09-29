-- Prove2me | solution 1 for FiniteTriangular.sum_range_46
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:17:21.195497+00:00
-- url     : https://prove2.me/submissions/be3f303f-ed86-4d32-9f7a-8a2a54bc09f3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 46, k = 1035 := by
  decide
