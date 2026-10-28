-- Prove2me | solution 2 for AvramDividend.Classical.chat04_down_exit_time_pos_of_initial_safe_window
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:41:11.000994+00:00
-- url     : https://prove2.me/submissions/716c8227-10c7-4d12-b8e2-f6454f0642ec

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a : ℝ) (ω : Ω) (ε : ℝ≥0) (hε : 0 < ε)
    (hSafe : ∀ t : ℝ≥0, t < ε → -a ≤ X.X t ω) :
    0 < twoSidedExitDownTime X (-a) ω := by
  unfold twoSidedExitDownTime
  refine lt_of_lt_of_le (ENNReal.coe_pos.mpr hε) (le_iInf₂ fun t ht => ?_)
  by_contra h
  push_neg at h
  exact absurd (hSafe t (by exact_mod_cast h)) (not_le.mpr ht)
