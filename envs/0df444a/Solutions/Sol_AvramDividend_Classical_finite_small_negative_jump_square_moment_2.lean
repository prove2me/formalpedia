-- Prove2me | solution 2 for AvramDividend.Classical.finite_small_negative_jump_square_moment
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T14:37:25.678449+00:00
-- url     : https://prove2.me/submissions/4a9cf112-0bb9-41f1-ba84-d3166c254c48

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (ν : Measure ℝ)
    (hν : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal (y ^ 2) ∂ν) < ⊤ := by
  refine lt_of_le_of_lt (le_trans (lintegral_mono_ae ?_) (setLIntegral_le_lintegral _ _)) hν
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun y hy => ?_)
  exact ENNReal.ofReal_le_ofReal (le_min (by nlinarith [hy.1, hy.2]) le_rfl)
