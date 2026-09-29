-- Prove2me | solution 1 for FiniteTriangular.sum_range_810
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:30:05.970555+00:00
-- url     : https://prove2.me/submissions/e03baa84-27e2-47df-a173-3a494a2e92de

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 810, k = 327645 := by
  rw [sum_range_id]
