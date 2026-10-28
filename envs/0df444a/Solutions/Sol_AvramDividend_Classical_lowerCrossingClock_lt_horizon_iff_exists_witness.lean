-- Prove2me | solution 1 for AvramDividend.Classical.lowerCrossingClock_lt_horizon_iff_exists_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:02:29.333772+00:00
-- url     : https://prove2.me/submissions/7f512565-3ea8-4458-b4ad-13bd21543ebc

import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A strict downward first-passage infimum precedes a finite horizon
    exactly when a sample-path downward witness occurs before the horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower : ℝ)
    (ω : Ω) (u : ℝ≥0) :
    (⨅ (s : ℝ≥0) (_ : X.X s ω < lower), (s : ℝ≥0∞)) <
      (u : ℝ≥0∞) ↔
    ∃ s : ℝ≥0, s < u ∧ X.X s ω < lower := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (iInf_lt_iff).mp h
    obtain ⟨hneg, hslt⟩ := (iInf_lt_iff).mp hs
    exact ⟨s, (ENNReal.coe_lt_coe).mp hslt, hneg⟩
  · rintro ⟨s, hs, hneg⟩
    apply (iInf_lt_iff).mpr
    refine ⟨s, (iInf_lt_iff).mpr ?_⟩
    exact ⟨hneg, (ENNReal.coe_lt_coe).mpr hs⟩
