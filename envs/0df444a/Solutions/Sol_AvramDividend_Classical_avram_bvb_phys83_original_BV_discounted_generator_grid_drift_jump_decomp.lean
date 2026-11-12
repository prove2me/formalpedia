-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys83_original_BV_discounted_generator_grid_drift_jump_decomp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:47:13.213216+00:00
-- url     : https://prove2.me/submissions/3b9ec587-7d21-410b-b2d2-fa0698769597

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_discounted_jump_drift_generator_residual
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- On each active BV grid cell, the discounted generator contribution
splits exactly into physical drift and its negative jump compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (q : ℝ) (s : Finset ℕ)
    (z t a : ℕ → ℝ)
    (hGen : ∀ i ∈ s, X.GeneratorIntegrable w (z i)) :
    (∑ i ∈ s,
       Real.exp (-(q * t i)) *
         (X.generator w (z i) - q * w (z i)) * a i) =
    (∑ i ∈ s,
       Real.exp (-(q * t i)) *
         (X.drift * deriv w (z i) - q * w (z i)) * a i) +
    (∑ i ∈ s,
       (∫ y in Iio (0 : ℝ), Real.exp (-(q * t i)) *
         (w (z i + y) - w (z i)) ∂X.ν) * a i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hgi : X.GeneratorIntegrable w (z i) := hGen i hi
  have hjump := avram_p3_b_bvjump_original_discounted_jump_drift_generator_residual
    X hBV w (z i) q (t i) hgi
  rw [hjump]
  ring
