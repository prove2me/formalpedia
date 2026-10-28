-- Prove2me | solution 1 for AvramDividend.Classical.chat04_up_exit_time_pos_of_initial_safe_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:27:05.834998+00:00
-- url     : https://prove2.me/submissions/eaac3666-d6f5-4a8b-8baf-1440955135bd

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! A strictly positive safety window prevents instantaneous upward passage. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (ω : Ω) (ε : ℝ≥0) (hε : 0 < ε)
    (hSafe : ∀ t : ℝ≥0, t < ε → X.X t ω ≤ b) :
    0 < twoSidedExitUpTime X b ω := by
  unfold twoSidedExitUpTime
  refine lt_of_lt_of_le (ENNReal.coe_pos.mpr hε) (le_iInf₂ fun t ht => ?_)
  by_contra h
  push_neg at h
  exact absurd ht (not_lt.mpr (hSafe t (by exact_mod_cast h)))
