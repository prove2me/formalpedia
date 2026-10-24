-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_exit_clocks_monotone_initial_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:03:18.499134+00:00
-- url     : https://prove2.me/submissions/bf6cec82-d607-4c74-8e66-62d0bc03ad86

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Increasing the starting reserve advances strict upward exit and delays ruin. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a x y : ℝ) (hxy : x ≤ y) (ω : Ω) :
    twoSidedExitUpTime X (a - y) ω ≤ twoSidedExitUpTime X (a - x) ω ∧
    twoSidedExitDownTime X (-x) ω ≤ twoSidedExitDownTime X (-y) ω := by
  constructor
  · have hb : a - y ≤ a - x := sub_le_sub_left hxy a
    change (⨅ t : ℝ≥0, ⨅ _ : a - y < X.X t ω, (t : ℝ≥0∞)) ≤
      (⨅ t : ℝ≥0, ⨅ _ : a - x < X.X t ω, (t : ℝ≥0∞))
    refine le_iInf fun t => le_iInf fun ht => ?_
    exact iInf_le_of_le t (iInf_le _ (lt_of_le_of_lt hb ht))
  · have hb : -y ≤ -x := neg_le_neg hxy
    change (⨅ t : ℝ≥0, ⨅ _ : X.X t ω < -x, (t : ℝ≥0∞)) ≤
      (⨅ t : ℝ≥0, ⨅ _ : X.X t ω < -y, (t : ℝ≥0∞))
    refine le_iInf fun t => le_iInf fun ht => ?_
    exact iInf_le_of_le t (iInf_le _ (lt_of_lt_of_le ht hb))
