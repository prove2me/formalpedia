-- Prove2me | solution 1 for FiniteTriangular.sum_range_475
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:15:37.108461+00:00
-- url     : https://prove2.me/submissions/28b8c5c7-1686-4561-ab40-e6ade48236a2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 475, k = 112575 := by
  rw [sum_range_id]
