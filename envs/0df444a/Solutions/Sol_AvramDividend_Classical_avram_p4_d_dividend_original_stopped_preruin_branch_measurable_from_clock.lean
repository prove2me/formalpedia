-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_stopped_preruin_branch_measurable_from_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:12:32.555455+00:00
-- url     : https://prove2.me/submissions/c4df2c9e-1779-49e2-9235-065a65c1e24e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original stopped dividend branch is measurable at the source
clock, including the initial-payment alternative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ))) :
    MeasurableSet {ω : Ω | τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω} := by
  have hτcast : Measurable (fun ω : Ω => (τ ω : ℝ≥0∞)) := by
    simpa [Function.comp_def, ENNReal.ofReal_coe_nnreal] using
      (ENNReal.measurable_ofReal.comp hτmeas)
  have hRuin : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hD.1.1
  have hZero : MeasurableSet {ω : Ω | (τ ω : ℝ≥0∞) = 0} := by
    change MeasurableSet ((fun ω : Ω => (τ ω : ℝ≥0∞)) ⁻¹' {0})
    exact (measurableSet_singleton (0 : ℝ≥0∞)).preimage hτcast
  have hBefore : MeasurableSet {ω : Ω |
      (τ ω : ℝ≥0∞) < ruinTime X x D ω} :=
    measurableSet_lt hτcast hRuin
  have hUnion := hZero.union hBefore
  convert hUnion using 1
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro (h | h)
    · left
      simpa [h]
    · exact Or.inr h
  · rintro (h | h)
    · left
      exact_mod_cast h
    · exact Or.inr h
