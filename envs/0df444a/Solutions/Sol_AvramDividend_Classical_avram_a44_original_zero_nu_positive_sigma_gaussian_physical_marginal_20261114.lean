-- Prove2me | solution 1 for AvramDividend.Classical.avram_a44_original_zero_nu_positive_sigma_gaussian_physical_marginal_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:29:56.882262+00:00
-- url     : https://prove2.me/submissions/b746ddea-b01c-4018-ae13-6049747634ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a40_original_zero_nu_intrinsic_gaussian_normalised_exact_law_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a31_original_gaussian_source_ae_representative_measurable_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hNu : X.ν = 0) (hPositive : 0 < X.σ)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ t : ℝ≥0,
      Measure.map (R t) P =
        gaussianReal 0
          ((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * t) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, R t ω = R t ω := by
    filter_upwards [] with ω
    intro t
    rfl
  have hMeas :=
    avram_a31_original_gaussian_source_ae_representative_measurable_20261114
      X R hR R hEq
  intro t
  let Z : Ω → ℝ := fun ω => R t ω / X.σ
  have hZ : AEMeasurable Z P := (hMeas t).div_const X.σ
  have hNorm : HasLaw Z (gaussianReal 0 t) P :=
    ⟨hZ, avram_a40_original_zero_nu_intrinsic_gaussian_normalised_exact_law_20261114
      X hNu hPositive R hR t⟩
  have hScaled := gaussianReal_mul_const hNorm X.σ
  have hPath : (fun ω => Z ω * X.σ) = R t := by
    funext ω
    dsimp [Z]
    field_simp
  rw [hPath] at hScaled
  simpa only [mul_zero, zero_add] using hScaled.map_eq
