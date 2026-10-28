-- Prove2me | solution 1 for AvramDividend.Classical.chat12_scale_right_ratio_nonneg_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:56:40.45745+00:00
-- url     : https://prove2.me/submissions/a4bf0576-dc94-4b0a-b779-e14e6a58e6ff

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

theorem solution
    (W : ℝ → ℝ) (a ε : ℝ)
    (hWa : 0 ≤ W a) (hWright : 0 < W (a + ε))
    (hWinc : W a < W (a + ε)) :
    0 ≤ W a / W (a + ε) ∧ W a / W (a + ε) < 1 := by
  constructor
  · exact div_nonneg hWa (le_of_lt hWright)
  · exact (div_lt_one hWright).2 hWinc
