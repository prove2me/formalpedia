-- Prove2me | solution 1 for FiniteTriangular.sum_range_1095
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:24:02.371876+00:00
-- url     : https://prove2.me/submissions/56ecce08-2bf5-4a74-b6e5-45cb0470c628

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1095, k = 598965 := by
  rw [sum_range_id]
