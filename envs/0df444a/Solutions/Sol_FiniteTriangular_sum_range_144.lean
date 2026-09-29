-- Prove2me | solution 1 for FiniteTriangular.sum_range_144
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:16:21.165986+00:00
-- url     : https://prove2.me/submissions/a5a2186c-a62f-4ef5-8699-691b0c46cf01

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 144, k = 10296 := by
  rw [sum_range_id]
