-- Prove2me | solution 1 for FiniteTriangular.sum_range_43
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:17:18.908927+00:00
-- url     : https://prove2.me/submissions/8dfebc4b-5448-4451-8367-76ca1ad7149c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 43, k = 903 := by
  decide
