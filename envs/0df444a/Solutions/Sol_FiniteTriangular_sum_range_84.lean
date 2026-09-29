-- Prove2me | solution 1 for FiniteTriangular.sum_range_84
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:40:14.955533+00:00
-- url     : https://prove2.me/submissions/082c117d-4991-473b-8726-98349292fbec

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 84, k = 3486 := by
  decide
