-- Prove2me | solution 1 for FiniteTriangular.sum_range_17
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:04:12.847982+00:00
-- url     : https://prove2.me/submissions/1375809b-93c2-4826-8c55-9f233f24be6b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 17, k = 136 := by
  decide
