-- Prove2me | solution 1 for FiniteTriangular.sum_range_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:01:06.365794+00:00
-- url     : https://prove2.me/submissions/0dbcb937-441d-43b2-9c08-184f614c4945

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 3, k = 3 := by
  decide
