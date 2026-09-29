-- Prove2me | solution 1 for FiniteTriangular.sum_range_63
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:21:38.486335+00:00
-- url     : https://prove2.me/submissions/c757467c-ead6-4500-a2a7-51c25317b1ea

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 63, k = 1953 := by
  decide
