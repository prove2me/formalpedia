-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18i_zero_cutoff_square_integrable_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:59:42.546844+00:00
-- url     : https://prove2.me/submissions/24609d3b-926e-4da9-875f-7c0e6cb714db

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

/-- Quadratic integrability is determined by the original cutoff-zero
residual law, hence transfers across equal Lévy triplets. -/
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (t : ℝ≥0)
    (hY : Integrable (fun ω : Ω₂ => (avram_p4_h_gaussian_intrinsic_truncated_residual Y 0 t ω) ^ 2) P₂) :
    Integrable (fun ω : Ω₁ => (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2) P₁ := by
  let fX : Ω₁ → ℝ := fun ω =>
    (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2
  let fY : Ω₂ → ℝ := fun ω =>
    (avram_p4_h_gaussian_intrinsic_truncated_residual Y 0 t ω) ^ 2
  have hMeasX : Measurable fX :=
    ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X 0 t).mono (𝓕₁.le t) le_rfl).pow_const 2
  have hMeasY : Measurable fY :=
    ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      Y 0 t).mono (𝓕₂.le t) le_rfl).pow_const 2
  have hYmap : Integrable (fun z : ℝ => z) (P₂.map fY) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable
      hMeasY.aemeasurable).2 (by simpa [Function.comp_def, fY] using hY)
  have hLaw : P₁.map fX = P₂.map fY :=
    avram_ja18i_zero_cutoff_square_law_of_equal_triplet X Y hc hσ hν t
  have hXmap : Integrable (fun z : ℝ => z) (P₁.map fX) := by
    rw [hLaw]
    exact hYmap
  exact (integrable_map_measure measurable_id.aestronglyMeasurable
    hMeasX.aemeasurable).mp hXmap
