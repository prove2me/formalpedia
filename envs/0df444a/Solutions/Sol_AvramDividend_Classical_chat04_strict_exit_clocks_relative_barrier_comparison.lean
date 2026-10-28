-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_exit_clocks_relative_barrier_comparison
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:36:08.73326+00:00
-- url     : https://prove2.me/submissions/abdcaa7e-1b08-40b1-a3df-437176028947

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The strict upper exit moves earlier and lower ruin later when reserve gain covers the increase in barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b x y : ℝ) (hxy : x ≤ y) (hrel : b - y ≤ a - x)
    (ω : Ω) :
    twoSidedExitUpTime X (b - y) ω ≤ twoSidedExitUpTime X (a - x) ω ∧
    twoSidedExitDownTime X (-x) ω ≤ twoSidedExitDownTime X (-y) ω := by
  constructor
  · change (⨅ t : ℝ≥0, ⨅ _ : b - y < X.X t ω, (t : ℝ≥0∞)) ≤
      (⨅ t : ℝ≥0, ⨅ _ : a - x < X.X t ω, (t : ℝ≥0∞))
    refine le_iInf fun t => le_iInf fun ht => ?_
    exact iInf_le_of_le t (iInf_le _ (lt_of_le_of_lt hrel ht))
  · have hb : -y ≤ -x := neg_le_neg hxy
    change (⨅ t : ℝ≥0, ⨅ _ : X.X t ω < -x, (t : ℝ≥0∞)) ≤
      (⨅ t : ℝ≥0, ⨅ _ : X.X t ω < -y, (t : ℝ≥0∞))
    refine le_iInf fun t => le_iInf fun ht => ?_
    exact iInf_le_of_le t (iInf_le _ (lt_of_lt_of_le ht hb))
