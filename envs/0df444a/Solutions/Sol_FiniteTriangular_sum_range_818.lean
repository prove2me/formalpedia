-- Prove2me | solution 1 for FiniteTriangular.sum_range_818
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:31:54.087982+00:00
-- url     : https://prove2.me/submissions/0d9719d7-7c0c-472a-8333-9cc9f9332200

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 818, k = 334153 := by
  rw [sum_range_id]
