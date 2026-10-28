-- Prove2me | solution 1 for FeynmanKac.augmented_coefficients_all_time_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T10:33:08.328002+00:00
-- url     : https://prove2.me/submissions/ffb19be8-441d-41a1-af68-7f900952f46c

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Theorems.Thm_FeynmanKac_clock_coordinate_all_nonnegative_ae
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P) :
    ∀ᵐ ω ∂P, ∀ (r : ℝ), 0 ≤ r →
      m.augmentedDrift (m.augmentedPath r ω) (0 : Fin 2) =
        m.drift (m.path (m.initialTime + r) ω) (m.initialTime + r) ∧
      m.augmentedVolatility (m.augmentedPath r ω) 0 (0 : Fin 2) =
        m.volatility (m.path (m.initialTime + r) ω) (m.initialTime + r) := by
  have hclock := FeynmanKac.clock_coordinate_all_nonnegative_ae P m
  filter_upwards [hclock] with ω hω
  intro r hr
  have htime := hω r hr
  constructor
  · calc
      m.augmentedDrift (m.augmentedPath r ω) 0 =
          m.drift (m.augmentedPath r ω 0) (m.augmentedPath r ω 1) :=
        m.augmentedDrift_space _
      _ = m.drift (m.path (m.initialTime + r) ω)
          (m.initialTime + r) := by
        simp [FeynmanKac.BoundedDiffusionModel.path, htime]
  · calc
      m.augmentedVolatility (m.augmentedPath r ω) 0 0 =
          m.volatility (m.augmentedPath r ω 0)
            (m.augmentedPath r ω 1) :=
        m.augmentedVolatility_space _
      _ = m.volatility (m.path (m.initialTime + r) ω)
          (m.initialTime + r) := by
        simp [FeynmanKac.BoundedDiffusionModel.path, htime]
