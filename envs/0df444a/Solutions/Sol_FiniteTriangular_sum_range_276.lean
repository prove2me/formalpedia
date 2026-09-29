-- Prove2me | solution 1 for FiniteTriangular.sum_range_276
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:14:54.239982+00:00
-- url     : https://prove2.me/submissions/f9b3046e-a1c4-45f2-b4cf-00d22966d824

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 276, k = 37950 := by
  rw [sum_range_id]
