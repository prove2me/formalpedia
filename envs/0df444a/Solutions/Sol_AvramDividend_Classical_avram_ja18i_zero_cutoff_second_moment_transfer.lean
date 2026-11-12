-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18i_zero_cutoff_second_moment_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:11:09.335278+00:00
-- url     : https://prove2.me/submissions/3c74b71e-3954-4303-b08d-c9407368fa98

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18i_zero_cutoff_square_law_of_equal_triplet
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The expected quadratic residual transfers across equal original triplets. -/
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (t : ℝ≥0) :
    (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2 ∂P₁) =
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual Y 0 t ω) ^ 2 ∂P₂) := by
  let fX : Ω₁ → ℝ := fun ω =>
    (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2
  let fY : Ω₂ → ℝ := fun ω =>
    (avram_p4_h_gaussian_intrinsic_truncated_residual Y 0 t ω) ^ 2
  have hMX : Measurable fX :=
    ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X 0 t).mono (𝓕₁.le t) le_rfl).pow_const 2
  have hMY : Measurable fY :=
    ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      Y 0 t).mono (𝓕₂.le t) le_rfl).pow_const 2
  have hLaw : P₁.map fX = P₂.map fY :=
    avram_ja18i_zero_cutoff_square_law_of_equal_triplet X Y hc hσ hν t
  change (∫ ω, fX ω ∂P₁) = ∫ ω, fY ω ∂P₂
  calc
    (∫ ω, fX ω ∂P₁) = ∫ z : ℝ, z ∂(P₁.map fX) := by
      simpa [Function.comp_def] using
        (integral_map (μ := P₁) (φ := fX)
          hMX.aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = ∫ z : ℝ, z ∂(P₂.map fY) := by rw [hLaw]
    _ = ∫ ω, fY ω ∂P₂ := by
      simpa [Function.comp_def] using
        (integral_map (μ := P₂) (φ := fY)
          hMY.aemeasurable measurable_id.aestronglyMeasurable)
