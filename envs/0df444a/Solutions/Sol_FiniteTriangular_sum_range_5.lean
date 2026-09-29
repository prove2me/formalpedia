-- Prove2me | solution 1 for FiniteTriangular.sum_range_5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T18:56:05.1679+00:00
-- url     : https://prove2.me/submissions/00a09309-a57e-4e99-a561-d5f5134ed43e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 5, k = 10 := by
  decide
