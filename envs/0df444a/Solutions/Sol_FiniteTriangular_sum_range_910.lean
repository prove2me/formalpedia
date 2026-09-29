-- Prove2me | solution 1 for FiniteTriangular.sum_range_910
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:50:24.031643+00:00
-- url     : https://prove2.me/submissions/2ec7e339-31a9-4b8b-911b-868ea61d8288

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 910, k = 413595 := by
  rw [sum_range_id]
