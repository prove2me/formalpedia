-- Prove2me | solution 1 for FiniteTriangular.sum_range_80
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:38:23.929982+00:00
-- url     : https://prove2.me/submissions/e9e4196c-e549-4cd8-ad1a-fbff64b89c16

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 80, k = 3160 := by
  decide
