-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_lt_iff_exists_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:46:49.23233+00:00
-- url     : https://prove2.me/submissions/076c6be8-3ea3-43d7-bb8f-1afa24e1c052

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (ω : Ω) (t : ℝ≥0) :
    (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)) < (t : ℝ≥0∞) ↔
      ∃ s : ℝ≥0, b < X.X s ω ∧ s < t := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (iInf_lt_iff).mp h
    obtain ⟨hgt, hst⟩ := (iInf_lt_iff).mp hs
    exact ⟨s, hgt, (ENNReal.coe_lt_coe).mp hst⟩
  · rintro ⟨s, hgt, hst⟩
    exact (iInf_lt_iff).mpr
      ⟨s, (iInf_lt_iff).mpr
        ⟨hgt, (ENNReal.coe_lt_coe).mpr hst⟩⟩
