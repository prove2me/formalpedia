-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_eventually_strict_survival_of_clock_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:46:52.539918+00:00
-- url     : https://prove2.me/submissions/829524c8-0cce-476c-8cce-119bcc90c51c

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

/-- Convergent finite clocks eventually preserve the genuine strict pre-ruin test. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (t : ℝ≥0) (ht : (t : ℝ≥0∞) < ruinTime X x D ω)
    (τ : ℕ → ℝ≥0)
    (hτ : Filter.Tendsto τ Filter.atTop (𝓝 t)) :
    ∀ᶠ n in Filter.atTop, (τ n : ℝ≥0∞) < ruinTime X x D ω := by
  have hOpen : IsOpen
      {s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω} := by
    have hIio : IsOpen (Iio (ruinTime X x D ω)) := isOpen_Iio
    simpa only [Set.preimage, Set.mem_Iio] using
      hIio.preimage ENNReal.continuous_coe
  have hEvent : ∀ᶠ n in Filter.atTop,
      τ n ∈ {s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω} :=
    hτ.eventually (hOpen.mem_nhds ht)
  simpa only [Set.mem_setOf_eq] using hEvent
