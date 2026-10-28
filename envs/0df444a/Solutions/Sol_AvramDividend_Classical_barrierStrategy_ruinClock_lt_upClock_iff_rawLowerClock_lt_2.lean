-- Prove2me | solution 2 for AvramDividend.Classical.barrierStrategy_ruinClock_lt_upClock_iff_rawLowerClock_lt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:27:32.072983+00:00
-- url     : https://prove2.me/submissions/3329c4b5-eecb-4049-b45f-209c6bccf3aa

import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_preUpcrossingRuin_iff_lowerClockBefore
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The controlled ruin clock precedes a finite first upper barrier crossing
    exactly when the raw Levy path's lower exit clock does so. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    ruinTime X x (barrierStrategy X x a) ω < (u : ℝ≥0∞) ↔
      (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) <
        (u : ℝ≥0∞) := by
  have htime :
      ruinTime X x (barrierStrategy X x a) ω < (u : ℝ≥0∞) ↔
        ∃ s : ℝ≥0, s < u ∧
          riskProcess X x (barrierStrategy X x a) s ω < 0 := by
    unfold ruinTime
    constructor
    · intro h
      obtain ⟨s, hs⟩ := (iInf_lt_iff).mp h
      obtain ⟨hneg, hslt⟩ := (iInf_lt_iff).mp hs
      exact ⟨s, (ENNReal.coe_lt_coe).mp hslt, hneg⟩
    · rintro ⟨s, hs, hneg⟩
      apply (iInf_lt_iff).mpr
      refine ⟨s, (iInf_lt_iff).mpr ?_⟩
      exact ⟨hneg, (ENNReal.coe_lt_coe).mpr hs⟩
  rw [htime]
  exact barrierStrategy_preUpcrossingRuin_iff_lowerClockBefore X x a ω u hu