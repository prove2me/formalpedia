-- Prove2me | solution 1 for AvramDividend.Classical.boundedVariation_physical_hjb_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:43:44.390896+00:00
-- url     : https://prove2.me/submissions/28c7c26a-18a1-4440-aa56-b163736907a6

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_hjb_component_inequalities
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Finite-variation HJB budget with the physical drift and raw negative jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 < x) (hxC : ENNReal.ofReal x < C) :
    IntegrableOn (fun y : ℝ => w (x + y) - w x) (Iio (0 : ℝ)) X.ν ∧
      X.drift * deriv w x +
          (∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν) ≤ q * w x ∧
      1 ≤ deriv w x := by
  obtain ⟨hGen, hGamma, hGrad⟩ :=
    hjb_component_inequalities X q w C hw_hjb x hx hxC
  refine ⟨boundedVariation_full_negative_jump_increment_integrable X hBV w x hGen, ?_, hGrad⟩
  rw [boundedVariation_generator_physical_drift_representation X hBV w x hGen] at hGamma
  linarith
