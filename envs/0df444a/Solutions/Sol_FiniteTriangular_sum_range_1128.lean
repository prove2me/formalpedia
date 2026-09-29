-- Prove2me | solution 1 for FiniteTriangular.sum_range_1128
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:30:45.447992+00:00
-- url     : https://prove2.me/submissions/c917b129-3493-4f12-81b4-996d3a30a25c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1128, k = 635628 := by
  rw [sum_range_id]
