-- Prove2me | solution 1 for FiniteTriangular.sum_range_13
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:04:08.190389+00:00
-- url     : https://prove2.me/submissions/6655d1c7-d60e-44a7-936c-3eeaa2105698

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 13, k = 78 := by
  decide
