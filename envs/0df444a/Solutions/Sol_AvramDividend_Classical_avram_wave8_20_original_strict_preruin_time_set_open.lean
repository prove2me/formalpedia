-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_strict_preruin_time_set_open
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:38:43.501834+00:00
-- url     : https://prove2.me/submissions/3231d5e5-2cb0-4d9c-a813-24b3e4f3a4bd

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strict survival has an open physical-time domain on each source path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ruinTime X x D ω} := by
  have hopen : IsOpen (Iio (ruinTime X x D ω)) :=
    isOpen_Iio
  simpa only [Set.preimage, Set.mem_Iio] using
    hopen.preimage ENNReal.continuous_coe
