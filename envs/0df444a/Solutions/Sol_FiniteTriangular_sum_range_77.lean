-- Prove2me | solution 1 for FiniteTriangular.sum_range_77
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:38:21.633495+00:00
-- url     : https://prove2.me/submissions/1f090c0b-9adb-49e5-b53e-87767c74f56b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 77, k = 2926 := by
  decide
