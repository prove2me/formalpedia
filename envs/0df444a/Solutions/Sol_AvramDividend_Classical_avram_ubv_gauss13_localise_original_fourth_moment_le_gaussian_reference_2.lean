-- Prove2me | solution 2 for AvramDividend.Classical.avram_ubv_gauss13_localise_original_fourth_moment_le_gaussian_reference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:22:42.171375+00:00
-- url     : https://prove2.me/submissions/6d223216-83c7-4087-9811-96d23b93355b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_gaussian_fourth_moment_positive_fatou
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_gaussianReal_fourth_positive_tilt_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ) (t : ℝ≥0)
    (hMeas : Measurable (fun ω : Ω =>
      (X.X t ω - (t : ℝ) * X.c) / X.σ)) :
    (∫⁻ ω, ENNReal.ofReal
      (((X.X t ω - (t : ℝ) * X.c) / X.σ) ^ 4) ∂P) ≤
    ENNReal.ofReal (∫ z : ℝ, z ^ 4 ∂(gaussianReal 0 t)) := by
  have hT := avram_ubv_gauss13_localise_gaussianReal_fourth_positive_tilt_tendsto_zero t
  have hOfReal : Tendsto (fun n : ℕ => ENNReal.ofReal
      (∫ z : ℝ, z ^ 4 * Real.exp ((1 / ((n : ℝ) + 1)) * z)
        ∂(gaussianReal 0 t))) atTop
      (𝓝 (ENNReal.ofReal (∫ z : ℝ, z ^ 4 ∂(gaussianReal 0 t)))) := by
    exact (ENNReal.continuous_ofReal.tendsto _).comp hT
  calc
    (∫⁻ ω, ENNReal.ofReal
      (((X.X t ω - (t : ℝ) * X.c) / X.σ) ^ 4) ∂P) ≤
        Filter.liminf (fun n : ℕ => ENNReal.ofReal
          (∫ z : ℝ, z ^ 4 * Real.exp ((1 / ((n : ℝ) + 1)) * z)
            ∂(gaussianReal 0 t))) atTop :=
      avram_ubv_gauss13_localise_original_gaussian_fourth_moment_positive_fatou
        X hν hσ t hMeas
    _ = ENNReal.ofReal (∫ z : ℝ, z ^ 4 ∂(gaussianReal 0 t)) :=
      hOfReal.liminf_eq
