-- Prove2me | solution 1 for FiniteTriangular.sum_range_1061
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:17:02.987437+00:00
-- url     : https://prove2.me/submissions/dae91b8b-c409-4872-bfcb-7859561e7d8c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1061, k = 562330 := by
  rw [sum_range_id]
