-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_grid_to_intrinsic_real_l2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:56:40.706233+00:00
-- url     : https://prove2.me/submissions/b4556389-8e91-4284-8167-1f9cfc264dfd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_intrinsic_limit_fatou_from_finite_grid
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_intrinsic_real_l2_from_physical_energy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_exact_pair_strip_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One genuine original-process interface: a finite-grid physical L²
bound and mesh limit yield the intrinsic real L² isometry inequality.
The original square measurability remains a source obligation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n m : ℕ)
    (G : ℕ → Ω → ℝ≥0∞)
    (hMeas : ∀ k, Measurable (G k))
    (hSourceLimit : ∀ᵐ ω ∂P,
      Tendsto (fun k => G k ω) atTop
        (𝓝 (ENNReal.ofReal
          ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2))))
    (hSourceFiniteGrid : ∀ k,
      (∫⁻ ω, G k ω ∂P) ≤ (T : ℝ≥0∞) *
        (∫⁻ z in Ioc
          (-(1 / (((min n m : ℕ) : ℝ) + 1)))
          (-(1 / (((max n m : ℕ) : ℝ) + 1))),
          ENNReal.ofReal (z ^ 2) ∂X.ν))
    (hSquareAE : AEStronglyMeasurable (fun ω : Ω =>
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) P) :
    Integrable (fun ω : Ω =>
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) P ∧
    (∫ ω : Ω,
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2 ∂P) ≤
      (T : ℝ) * (∫ z in Ioc
        (-(1 / (((min n m : ℕ) : ℝ) + 1)))
        (-(1 / (((max n m : ℕ) : ℝ) + 1))), z ^ 2 ∂X.ν) := by
  have hEnergy :=
    avram_p4_h_gaussian_original_nu_exact_pair_strip_integrable X n m
  have hFatou :=
    avram_p4_h_gaussian_original_intrinsic_limit_fatou_from_finite_grid
      X T n m G hMeas hSourceLimit hSourceFiniteGrid
  exact avram_p4_h_gaussian_original_intrinsic_real_l2_from_physical_energy
    X T n m hEnergy hSquareAE hFatou
