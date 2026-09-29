-- Prove2me | solution 1 for FiniteTriangular.sum_range_1031
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:45:58.103982+00:00
-- url     : https://prove2.me/submissions/1049f249-530e-4b21-8724-28e53d4d9605

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1031, k = 530965 := by
  rw [sum_range_id]
