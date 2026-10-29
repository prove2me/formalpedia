-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_grid_NNReal_coe_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:12:38.945989+00:00
-- url     : https://prove2.me/submissions/36beee51-1e08-498a-aee2-5025f0bdf809

import Mathlib
import Definitions.Def_AvramDividend_Classical_BvFiniteGridClocks_ws01c

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (H : ℝ≥0) (L : List ℝ≥0) (ω : Ω) :
    ((bv_finite_grid_below_NNReal_ws01c Y b H L ω : ℝ≥0) :
      WithTop ℝ≥0) =
      bv_finite_grid_below_clock_ws01c Y b H L ω := by
  unfold bv_finite_grid_below_NNReal_ws01c bv_finite_grid_below_clock_ws01c
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.foldr_cons]
    rw [← ih, WithTop.coe_min]
    split_ifs <;> rfl
