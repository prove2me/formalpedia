-- Prove2me | solution 1 for AvramDividend.Classical.bv_real_toNNReal_measurable_explicit_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:27:43.958985+00:00
-- url     : https://prove2.me/submissions/b4e5542d-42bf-46ef-8c65-8153b7a55899

import Mathlib
open MeasureTheory
open scoped NNReal
theorem solution :
    Measurable (Real.toNNReal : ℝ → ℝ≥0) := measurable_real_toNNReal
