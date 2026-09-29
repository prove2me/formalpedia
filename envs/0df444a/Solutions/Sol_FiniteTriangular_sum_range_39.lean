-- Prove2me | solution 1 for FiniteTriangular.sum_range_39
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:15:15.509823+00:00
-- url     : https://prove2.me/submissions/1f9a291c-96bf-4e25-912b-1c2acdf39ca2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 39, k = 741 := by
  decide
