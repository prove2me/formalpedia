-- Prove2me | solution 1 for FiniteTriangular.sum_range_921
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:53:44.664167+00:00
-- url     : https://prove2.me/submissions/41d9bbdc-b210-414d-8b13-a664f3b93f20

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 921, k = 423660 := by
  rw [sum_range_id]
