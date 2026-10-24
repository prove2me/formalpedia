-- Prove2me | solution 1 for AvramDividend.Classical.generatorIntegrand_large_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:53:26.226858+00:00
-- url     : https://prove2.me/submissions/3c318a9f-acef-4b06-bdd3-42265850feee

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Algebra.Notation.Indicator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- For jumps at or below minus one the truncation indicator vanishes. -/
theorem solution
    (w : ℝ → ℝ) (x y : ℝ) (hy : y ≤ (-1 : ℝ)) :
    SpectrallyNegativeLevy.generatorIntegrand w x y =
      w (x + y) - w x := by
  have hy' : y ∉ Ioo (-1 : ℝ) 1 := by
    intro hm
    exact not_lt_of_ge hy hm.1
  simp [SpectrallyNegativeLevy.generatorIntegrand, Set.indicator_of_notMem hy']
