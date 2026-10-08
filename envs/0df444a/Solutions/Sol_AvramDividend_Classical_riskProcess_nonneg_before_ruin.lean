-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_nonneg_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T09:58:00.027221+00:00
-- url     : https://prove2.me/submissions/ace662d1-c664-4073-8a31-5b55b9e9a5db

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ riskProcess X x D t ω := by
  by_contra h
  have hneg : riskProcess X x D t ω < 0 := lt_of_not_ge h
  have hle : ruinTime X x D ω ≤ (t : ℝ≥0∞) := by
    unfold ruinTime
    exact iInf_le_of_le t (iInf_le_of_le hneg le_rfl)
  exact (not_lt_of_ge hle) ht
