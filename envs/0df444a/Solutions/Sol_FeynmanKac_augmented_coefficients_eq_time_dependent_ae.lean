-- Prove2me | solution 1 for FeynmanKac.augmented_coefficients_eq_time_dependent_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:17:17.930284+00:00
-- url     : https://prove2.me/submissions/c5d59578-390b-4fde-837b-9f32ea360b89

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Theorems.Thm_FeynmanKac_clock_coordinate_absolute_time
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (r : ℝ) (hr : 0 ≤ r) :
    (fun ω => m.augmentedDrift (m.augmentedPath r ω) (0 : Fin 2)) =ᵐ[P]
      (fun ω => m.drift (m.path (m.initialTime + r) ω) (m.initialTime + r)) ∧
    (fun ω => m.augmentedVolatility (m.augmentedPath r ω) 0 (0 : Fin 2)) =ᵐ[P]
      (fun ω => m.volatility (m.path (m.initialTime + r) ω) (m.initialTime + r)) := by
  obtain ⟨B, hB⟩ := m.augmentedDrift_bounded
  have hclock :=
    FeynmanKac.clock_coordinate_absolute_time P m
      m.augmentedDrift_continuous B hB r hr
  constructor
  · filter_upwards [hclock] with ω hω
    calc
      m.augmentedDrift (m.augmentedPath r ω) 0 =
          m.drift (m.augmentedPath r ω 0) (m.augmentedPath r ω 1) :=
        m.augmentedDrift_space _
      _ = m.drift (m.path (m.initialTime + r) ω)
          (m.initialTime + r) := by
        simp [FeynmanKac.BoundedDiffusionModel.path, hω]
  · filter_upwards [hclock] with ω hω
    calc
      m.augmentedVolatility (m.augmentedPath r ω) 0 0 =
          m.volatility (m.augmentedPath r ω 0)
            (m.augmentedPath r ω 1) :=
        m.augmentedVolatility_space _
      _ = m.volatility (m.path (m.initialTime + r) ω)
          (m.initialTime + r) := by
        simp [FeynmanKac.BoundedDiffusionModel.path, hω]
