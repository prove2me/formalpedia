-- Prove2me | solution 1 for AvramDividend.Classical.chat04_down_exit_time_pos_of_initial_safe_window
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:41:05.697983+00:00
-- url     : https://prove2.me/submissions/4f1c1b76-1d2e-4f0c-9b8a-983914d7b783

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a : ℝ) (ω : Ω) (ε : ℝ≥0) (hε : 0 < ε)
    (hSafe : ∀ t : ℝ≥0, t < ε → -a ≤ X.X t ω) :
    0 < twoSidedExitDownTime X (-a) ω := by
  have hBound :
      (ε : ℝ≥0∞) ≤ twoSidedExitDownTime X (-a) ω := by
    unfold twoSidedExitDownTime
    refine le_iInf fun t => ?_
    refine le_iInf fun ht => ?_
    have hεt : ε ≤ t := by
      by_contra hnt
      have htε : t < ε := lt_of_not_ge hnt
      exact (not_lt_of_ge (hSafe t htε)) ht
    exact_mod_cast hεt
  have hεpos : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := by
    exact_mod_cast hε
  exact lt_of_lt_of_le hεpos hBound
