-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_weighted_log_negative_mark_recovers_original_test
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:07:29.981806+00:00
-- url     : https://prove2.me/submissions/418c867f-3d76-4a0c-8430-e224ffde95fa

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- On every strictly negative original jump mark, the fourth-weighted
exponential pushforward and logarithmic inverse recover the original test. -/
theorem solution
    (f : ℝ → ℝ) (y : ℝ) (hy : y < 0) :
    (f (Real.log (Real.exp y)) / (Real.exp y - 1) ^ 4) *
      (Real.exp y - 1) ^ 4 = f y := by
  have hExp : Real.exp y < 1 := Real.exp_lt_one_iff.mpr hy
  have hDiff : Real.exp y - 1 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_lt hExp)
  have hNonzero : (Real.exp y - 1) ^ 4 ≠ 0 :=
    pow_ne_zero 4 hDiff
  rw [Real.log_exp, div_mul_cancel₀ _ hNonzero]
