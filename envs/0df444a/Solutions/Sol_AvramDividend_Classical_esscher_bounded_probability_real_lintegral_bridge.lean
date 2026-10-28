-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_probability_real_lintegral_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:01:02.719491+00:00
-- url     : https://prove2.me/submissions/a6ee9e82-9ca1-4116-a417-11a2a417b018

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal

/-- Bounded probability CDF expectations agree exactly in real and ENNReal form. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (hf : Measurable f)
    (h0 : ∀ ω, 0 ≤ f ω) (h1 : ∀ ω, f ω ≤ 1) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂Q) =
      ENNReal.ofReal (∫ ω, f ω ∂Q) := by
  have hbound : ∀ᵐ ω ∂Q, ‖f ω‖ ≤ (1 : ℝ) := by
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 ω)] using h1 ω
  have hInt : Integrable f Q :=
    (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable hbound
  exact (ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall h0)).symm
