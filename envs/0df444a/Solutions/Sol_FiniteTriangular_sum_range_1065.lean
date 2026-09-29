-- Prove2me | solution 1 for FiniteTriangular.sum_range_1065
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:18:46.568202+00:00
-- url     : https://prove2.me/submissions/3771c003-8862-4b74-b331-91683d811241

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1065, k = 566580 := by
  rw [sum_range_id]
