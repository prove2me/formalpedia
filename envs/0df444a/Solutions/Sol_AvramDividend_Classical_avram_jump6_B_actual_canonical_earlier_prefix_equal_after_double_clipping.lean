-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_canonical_earlier_prefix_equal_after_double_clipping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:02:27.378839+00:00
-- url     : https://prove2.me/submissions/84bee800-ed67-41db-b509-bed3f1b9d78a

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (j k i : ℕ) (ρ : ℝ≥0) (hi : i ≤ k) :
    min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))
      (min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ) =
    min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ := by
  have hfrac :
      (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) ≤
      (k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) := by
    gcongr
  rw [← min_assoc, min_eq_left hfrac]
