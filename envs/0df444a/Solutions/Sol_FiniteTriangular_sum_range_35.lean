-- Prove2me | solution 1 for FiniteTriangular.sum_range_35
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:15:10.771888+00:00
-- url     : https://prove2.me/submissions/957f1718-981b-4485-80b1-bc745df28605

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 35, k = 595 := by
  decide
