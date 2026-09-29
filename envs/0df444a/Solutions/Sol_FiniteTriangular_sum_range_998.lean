-- Prove2me | solution 1 for FiniteTriangular.sum_range_998
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:38:50.315289+00:00
-- url     : https://prove2.me/submissions/78de816f-5adb-401b-ae8a-6642c1370ced

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 998, k = 497503 := by
  rw [sum_range_id]
