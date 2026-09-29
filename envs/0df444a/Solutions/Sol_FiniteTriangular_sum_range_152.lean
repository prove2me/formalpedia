-- Prove2me | solution 1 for FiniteTriangular.sum_range_152
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:17:46.081253+00:00
-- url     : https://prove2.me/submissions/7c9d818e-a472-42dc-89ae-fd418d142b4c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 152, k = 11476 := by
  rw [sum_range_id]
