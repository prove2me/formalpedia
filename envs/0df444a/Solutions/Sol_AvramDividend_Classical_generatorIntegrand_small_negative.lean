-- Prove2me | solution 1 for AvramDividend.Classical.generatorIntegrand_small_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:52:47.309568+00:00
-- url     : https://prove2.me/submissions/8e0dce76-853e-4c62-8f8e-ee2bcb2c6405

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Algebra.Notation.Indicator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- For a small negative Lévy jump, the truncation indicator equals one, so the generator jump integrand contains the exact first-order compensation deriv w x multiplied by y. -/
theorem solution
    (w : ℝ → ℝ) (x y : ℝ) (hy : y ∈ Ioo (-1 : ℝ) 0) :
    SpectrallyNegativeLevy.generatorIntegrand w x y =
      w (x + y) - w x - deriv w x * y := by
  have hy' : y ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hy.1, lt_trans hy.2 zero_lt_one⟩
  simp [SpectrallyNegativeLevy.generatorIntegrand, Set.indicator_of_mem hy']
