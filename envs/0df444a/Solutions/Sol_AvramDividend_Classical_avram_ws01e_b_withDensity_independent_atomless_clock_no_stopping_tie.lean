-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_withDensity_independent_atomless_clock_no_stopping_tie
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:52:07.716411+00:00
-- url     : https://prove2.me/submissions/4afd5504-b1ba-469f-b45b-c8d12223e78b

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_independent_atomless_clock_no_stopping_age_tie

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (hAtomless : ∀ a : ℝ≥0, Q {η : Θ | e η = a} = 0)
    (w : Ω × Θ → ℝ≥0∞) :
    ((P.prod Q).withDensity w)
      {z : Ω × Θ | τ z.1 = e z.2} = 0 := by
  have hZero : (P.prod Q)
      {z : Ω × Θ | τ z.1 = e z.2} = 0 :=
    avram_ws01e_b_independent_atomless_clock_no_stopping_age_tie
      P Q τ hτ e he hAtomless
  exact (withDensity_absolutelyContinuous (P.prod Q) w) hZero
