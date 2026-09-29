-- Prove2me | solution 1 for FiniteTriangular.sum_range_252
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:09:16.087984+00:00
-- url     : https://prove2.me/submissions/fdea2545-44ce-4339-8666-d4c79fa483bd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 252, k = 31626 := by
  rw [sum_range_id]
