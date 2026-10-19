-- Prove2me | solution 1 for AvramDividend.Classical.ruinTime_le_of_nonnegative_before_first_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T11:20:47.736906+00:00
-- url     : https://prove2.me/submissions/c9894f0d-3fde-48bc-be83-b4cbc91aa085

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D B : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hpre : ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ riskProcess X x B t ω) :
    ruinTime X x D ω ≤ ruinTime X x B ω := by
  change ruinTime X x D ω ≤
    (⨅ (t : ℝ≥0) (_ : riskProcess X x B t ω < 0), (t : ℝ≥0∞))
  refine le_iInf fun t => le_iInf fun hb => ?_
  by_contra hn
  have ht : (t : ℝ≥0∞) < ruinTime X x D ω :=
    lt_of_not_ge hn
  exact (not_lt_of_ge (hpre t ht)) hb
