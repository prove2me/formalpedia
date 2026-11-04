-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_physical_K_joint_measurable_from_source_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:16:28.899463+00:00
-- url     : https://prove2.me/submissions/ae1d8774-0756-4167-b681-cbace14f4cb7

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_physical_K_joint_measurable_of_components
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_value_measurable_of_positive_continuity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The original BV physical generator is jointly measurable from its true half-line value regularity and measurable stopped reserve/jump kernel. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (K : ℝ≥0 → Ω → ℝ)
  (hK : ∀ t ω, K t ω =
    Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) +
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t + z) -
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t) ∂X.ν) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t)))
  (hYmeas : Measurable (fun p : ℝ≥0 × Ω =>
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.2 - rightLimit D s p.2) p.1))
  (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
  (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
  (hJMeas : Measurable (fun y : ℝ =>
    ∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν)) :
  Measurable (fun p : ℝ≥0 × Ω => K p.1 p.2) := by
  have hwMeas : Measurable w :=
    avram_wave8_22_original_BV_value_measurable_of_positive_continuity
      w hw_cont hw_neg
  exact avram_wave8_22_original_BV_physical_K_joint_measurable_of_components
    X q w x D K hK hYmeas (measurable_deriv w) hwMeas hJMeas
