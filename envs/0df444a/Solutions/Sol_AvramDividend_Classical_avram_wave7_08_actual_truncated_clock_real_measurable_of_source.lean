-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_actual_truncated_clock_real_measurable_of_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:30:17.639335+00:00
-- url     : https://prove2.me/submissions/34469e26-cbe5-4f57-a0fd-aacd564c0848

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (hRuinMeas : Measurable (ruinTime X x D)) :
    Measurable (fun ω => (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ)) := by
  have hmin : Measurable (fun ω => min (ruinTime X x D ω) (n : ℝ≥0∞)) :=
    hRuinMeas.min measurable_const
  have hτ : Measurable (fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :=
    ENNReal.measurable_toNNReal.comp hmin
  exact hτ.coe_nnreal_real
