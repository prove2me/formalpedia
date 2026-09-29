-- Prove2me | solution 1 for FiniteTriangular.sum_range_1024
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:44:12.861982+00:00
-- url     : https://prove2.me/submissions/47beed40-3fbb-4195-aa8f-c640f85b083a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1024, k = 523776 := by
  rw [sum_range_id]
