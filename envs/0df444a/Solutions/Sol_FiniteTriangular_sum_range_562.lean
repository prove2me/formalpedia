-- Prove2me | solution 1 for FiniteTriangular.sum_range_562
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:36:17.470558+00:00
-- url     : https://prove2.me/submissions/4b482404-02c6-4eb7-bea2-dde27a3153a3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 562, k = 157641 := by
  rw [sum_range_id]
