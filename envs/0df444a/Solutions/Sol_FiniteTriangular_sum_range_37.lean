-- Prove2me | solution 1 for FiniteTriangular.sum_range_37
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:15:12.957375+00:00
-- url     : https://prove2.me/submissions/7b81bf5a-b542-4936-8083-ba1a7a355442

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 37, k = 666 := by
  decide
