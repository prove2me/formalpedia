-- Prove2me | solution 1 for FiniteTriangular.sum_range_1072
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:18:50.957243+00:00
-- url     : https://prove2.me/submissions/a188483e-ddc5-4777-9bf8-93ae85676a49

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1072, k = 574056 := by
  rw [sum_range_id]
