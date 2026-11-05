-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_physical_grid_residual_l2_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:08:35.425139+00:00
-- url     : https://prove2.me/submissions/0f33be18-35e5-41d6-bf72-41363ee0ffa0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_grid_to_intrinsic_real_l2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_residual_L2_cauchy_from_physical_strip_isometry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physically verified source-grid estimates for each cutoff pair give
an L² Cauchy sequence of the actual original-path Gaussian residuals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (G : ℕ → ℕ → ℕ → Ω → ℝ≥0∞)
    (hMeas : ∀ n m k, Measurable (G n m k))
    (hSourceLimit : ∀ n m, ∀ᵐ ω ∂P,
      Tendsto (fun k => G n m k ω) atTop
        (𝓝 (ENNReal.ofReal
          ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2))))
    (hSourceFiniteGrid : ∀ n m k,
      (∫⁻ ω, G n m k ω ∂P) ≤ (T : ℝ≥0∞) *
        (∫⁻ z in Ioc
          (-(1 / (((min n m : ℕ) : ℝ) + 1)))
          (-(1 / (((max n m : ℕ) : ℝ) + 1))),
          ENNReal.ofReal (z ^ 2) ∂X.ν))
    (hSquareAE : ∀ n m, AEStronglyMeasurable (fun ω : Ω =>
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) P) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      Integrable (fun ω : Ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
         avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω) ^ 2) P ∧
      (∫ ω : Ω,
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
         avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω) ^ 2 ∂P) < ε := by
  apply avram_p4_h_gaussian_original_residual_L2_cauchy_from_physical_strip_isometry
    X T
  intro n m
  exact avram_p4_h_gaussian_original_grid_to_intrinsic_real_l2_isometry
    X T n m (G n m) (hMeas n m) (hSourceLimit n m)
    (hSourceFiniteGrid n m) (hSquareAE n m)
