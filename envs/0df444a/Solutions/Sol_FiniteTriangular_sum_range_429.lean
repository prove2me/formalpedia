-- Prove2me | solution 1 for FiniteTriangular.sum_range_429
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:55:52.068719+00:00
-- url     : https://prove2.me/submissions/24eb153b-a45b-4948-90ee-6f4ee69e13ab

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 429, k = 91806 := by
  rw [sum_range_id]
