-- Prove2me | solution 1 for FiniteTriangular.sum_range_103
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:45:38.933985+00:00
-- url     : https://prove2.me/submissions/d13030ea-6ee7-41ca-bbc3-c78849a432af

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 103, k = 5253 := by
  decide
