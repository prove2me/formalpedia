-- Prove2me | solution 1 for FiniteTriangular.sum_range_407
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:50:34.44917+00:00
-- url     : https://prove2.me/submissions/9128addd-52dd-4e93-9b0c-078f1cac44bf

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 407, k = 82621 := by
  rw [sum_range_id]
