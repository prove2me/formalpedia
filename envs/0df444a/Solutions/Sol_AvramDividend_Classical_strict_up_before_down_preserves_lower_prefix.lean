-- Prove2me | solution 1 for AvramDividend.Classical.strict_up_before_down_preserves_lower_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:53:53.554753+00:00
-- url     : https://prove2.me/submissions/da3ef14a-ae7d-4f5f-8c3b-e92ad2b35dec

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
/-! A strict upper-first exit excludes every earlier lower crossing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u d : ℝ) (ω : Ω)
    (hUp : twoSidedExitUpTime X u ω <
      twoSidedExitDownTime X d ω) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < twoSidedExitUpTime X u ω →
      d ≤ X.X t ω := by
  intro t ht
  by_contra hnot
  have hlt : X.X t ω < d := lt_of_not_ge hnot
  have hDown : twoSidedExitDownTime X d ω ≤ (t : ℝ≥0∞) := by
    change (⨅ (s : ℝ≥0) (_ : X.X s ω < d), (s : ℝ≥0∞)) ≤ (t : ℝ≥0∞)
    exact iInf_le_of_le t (iInf_le_of_le hlt le_rfl)
  exact (lt_asymm hUp (lt_of_le_of_lt hDown ht))
