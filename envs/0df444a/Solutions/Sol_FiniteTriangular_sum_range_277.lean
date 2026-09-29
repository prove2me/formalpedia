-- Prove2me | solution 1 for FiniteTriangular.sum_range_277
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:14:54.865308+00:00
-- url     : https://prove2.me/submissions/17946423-24b8-4890-b156-eaa7e524c8bd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 277, k = 38226 := by
  rw [sum_range_id]
