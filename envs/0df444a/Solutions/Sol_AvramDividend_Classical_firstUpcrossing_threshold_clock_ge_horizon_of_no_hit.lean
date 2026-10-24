-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_threshold_clock_ge_horizon_of_no_hit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:53:46.831199+00:00
-- url     : https://prove2.me/submissions/485fb053-0083-4145-95f7-e634f83f62e4

import Mathlib.Data.Real.Basic
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! An absence of first passage up to T bounds the strict first-passage clock below by T. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (T : ℝ≥0) (c : ℝ)
    (hNo : ∀ r : ℝ≥0, r ≤ T → ¬ c < X.X r ω) :
    (T : ℝ≥0∞) ≤
      ⨅ (r : ℝ≥0) (_ : c < X.X r ω), (r : ℝ≥0∞) := by
  refine le_iInf fun r => le_iInf fun hr => ?_
  have hTr : T ≤ r := by
    by_contra hnr
    exact hNo r (le_of_lt (lt_of_not_ge hnr)) hr
  exact ENNReal.coe_le_coe.mpr hTr
