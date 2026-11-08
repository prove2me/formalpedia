-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_ruinTime_positive_of_local_nonnegative_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:19:24.938521+00:00
-- url     : https://prove2.me/submissions/b8fff10e-9afd-4209-b784-0d3c592b3143

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The source ruin-time infimum cannot enter a nonnegative reserve interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (δ : ℝ≥0) (hδ : 0 < δ)
    (hlocal : ∀ t : ℝ≥0, t < δ → 0 ≤ riskProcess X x D t ω) :
    (0 : ℝ≥0∞) < ruinTime X x D ω := by
  have hbound : (δ : ℝ≥0∞) ≤ ruinTime X x D ω := by
    unfold ruinTime
    apply le_iInf
    intro t
    apply le_iInf
    intro hneg
    by_contra hnot
    have ht : t < δ := by
      by_contra hn
      have hδt : δ ≤ t := le_of_not_gt hn
      exact hnot (by exact_mod_cast hδt)
    exact (not_lt_of_ge (hlocal t ht)) hneg
  have hpos : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) := by exact_mod_cast hδ
  exact lt_of_lt_of_le hpos hbound
