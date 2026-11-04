-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_generator_physical_drift_interval_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:57:53.218693+00:00
-- url     : https://prove2.me/submissions/9e1b3a0a-ef6a-4fe1-a528-28cb93771d00

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- On the same BV source process, the generator uses the exact physical
drift found in the sample-path jump budget, with an explicit residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    (X.generator w x = X.drift * deriv w x +
      ∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν) ∧
    (∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      ∃ r : ℝ, 0 ≤ r ∧
        (∑' u : ℝ≥0,
          if s < u ∧ u ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal + r =
        (((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω))) := by
  exact ⟨boundedVariation_generator_physical_drift_representation X hBV w x hGen,
    avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder X hBV⟩
