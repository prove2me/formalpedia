-- Prove2me | solution 1 for FiniteTriangular.sum_range_106
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:47:22.866996+00:00
-- url     : https://prove2.me/submissions/4be07221-7eac-4069-abea-2fc710f5dc5e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 106, k = 5565 := by
  decide
