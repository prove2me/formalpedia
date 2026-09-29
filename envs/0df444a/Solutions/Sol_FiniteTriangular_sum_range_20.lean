-- Prove2me | solution 1 for FiniteTriangular.sum_range_20
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:08:36.241824+00:00
-- url     : https://prove2.me/submissions/483415da-6e7c-4bf4-bf3a-ea58849958d2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 20, k = 190 := by
  decide
