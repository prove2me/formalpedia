-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_interior_C1_compact_interval_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:44:03.253858+00:00
-- url     : https://prove2.me/submissions/9d4aa78d-4b26-4e9f-9afc-fb6fdcdb8c7e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal

/-- Every compact interval contained in the C1 region has a uniform
Lipschitz constant, providing the first-order BV small-jump envelope. -/
theorem solution (w : ℝ → ℝ) (s : Set ℝ)
    (hw : ContDiffOn ℝ 1 w s)
    (a b : ℝ) (hsub : Icc a b ⊆ s) :
    ∃ K : ℝ≥0, LipschitzOnWith K w (Icc a b) := by
  have hw' : ContDiffOn ℝ 1 w (Icc a b) := hw.mono hsub
  exact hw'.exists_lipschitzOnWith
    (by norm_num) (convex_Icc a b) isCompact_Icc
