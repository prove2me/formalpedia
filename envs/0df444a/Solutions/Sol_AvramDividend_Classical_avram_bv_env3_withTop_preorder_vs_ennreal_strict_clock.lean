-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_withTop_preorder_vs_ennreal_strict_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:05:55.940805+00:00
-- url     : https://prove2.me/submissions/c9396869-0074-43e3-aa09-eb2b78782796

import Mathlib.Data.ENNReal.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
noncomputable section

theorem solution (S : ℝ≥0) (τ : ℝ≥0∞) :
    ((WithTop.some S : ℝ≥0∞) < τ) ↔ ((S : ℝ≥0∞) < τ) := by
  cases τ with
  | top =>
      constructor
      · intro _
        exact ENNReal.coe_lt_top
      · intro _
        exact WithTop.coe_lt_top S
  | coe r =>
      exact (WithTop.coe_lt_coe (a := r) (b := S)).trans
        (ENNReal.coe_lt_coe (r := S) (q := r)).symm
