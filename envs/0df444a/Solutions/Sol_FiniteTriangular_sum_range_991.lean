-- Prove2me | solution 1 for FiniteTriangular.sum_range_991
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:37:07.687981+00:00
-- url     : https://prove2.me/submissions/013fd3e2-a9b2-4b27-86d5-e82a15961938

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 991, k = 490545 := by
  rw [sum_range_id]
