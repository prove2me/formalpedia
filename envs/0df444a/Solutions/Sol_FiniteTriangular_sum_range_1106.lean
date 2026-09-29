-- Prove2me | solution 1 for FiniteTriangular.sum_range_1106
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:27:31.225546+00:00
-- url     : https://prove2.me/submissions/ee136fb8-6578-4a86-bec5-8794fe0b7acb

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1106, k = 611065 := by
  rw [sum_range_id]
