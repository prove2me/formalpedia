-- Prove2me | solution 1 for FiniteTriangular.sum_range_1042
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:13:17.424598+00:00
-- url     : https://prove2.me/submissions/68890bf8-62b0-4e23-8288-96d8e4ecc6fb

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1042, k = 542361 := by
  rw [sum_range_id]
