-- Prove2me | solution 1 for FiniteTriangular.sum_range_1069
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:18:49.186301+00:00
-- url     : https://prove2.me/submissions/b6a9cc1a-01ab-40b9-94f8-2efc988bc904

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1069, k = 570846 := by
  rw [sum_range_id]
