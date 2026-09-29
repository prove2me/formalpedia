-- Prove2me | solution 1 for FiniteTriangular.sum_range_93
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:43:52.693636+00:00
-- url     : https://prove2.me/submissions/c5d400a2-5411-4db7-b1eb-17b2713c54a8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 93, k = 4278 := by
  decide
