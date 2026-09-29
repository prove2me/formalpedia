-- Prove2me | solution 1 for FiniteTriangular.sum_range_54
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:19:14.624986+00:00
-- url     : https://prove2.me/submissions/b6b5eb9f-56ae-49b0-a309-5004a04490c8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 54, k = 1431 := by
  decide
