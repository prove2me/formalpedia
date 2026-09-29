-- Prove2me | solution 1 for FiniteTriangular.sum_range_18
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:08:34.852977+00:00
-- url     : https://prove2.me/submissions/0a31b4f8-e6b3-48e7-9467-11ed98abbdbd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 18, k = 153 := by
  decide
