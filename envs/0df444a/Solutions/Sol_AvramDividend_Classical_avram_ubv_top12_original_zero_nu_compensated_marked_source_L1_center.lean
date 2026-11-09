-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top12_original_zero_nu_compensated_marked_source_L1_center
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:26:23.577118+00:00
-- url     : https://prove2.me/submissions/3f01dc99-0675-4949-82b0-593fa4a20c21

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_compensated_marked_source_zero_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- The true original zero-jump compensated source is an integrable centred
    random variable for any marked integrand, because it vanishes a.e. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧
        X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t))))
    (Λ : Measure ℝ≥0) (g : Ω → ℝ≥0 × ℝ → ℝ) :
    (let J : Ω → ℝ := fun ω =>
      (∫ p, g ω p ∂(NX ω)) -
      (∫ t, ∫ z, g ω (t, z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂Λ)
     Integrable J P ∧ (∫ ω, J ω ∂P) = 0) := by
  let J : Ω → ℝ := fun ω =>
    (∫ p, g ω p ∂(NX ω)) -
      (∫ t, ∫ z, g ω (t, z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂Λ)
  have hJ : J =ᵐ[P] (fun _ : Ω => (0 : ℝ)) :=
    avram_ubv_top12_original_zero_nu_compensated_marked_source_zero_ae
      X hNuZero NX hNX Λ g
  have hI : Integrable J P := (integrable_zero _ _ _).congr hJ.symm
  refine ⟨hI, ?_⟩
  simpa using (integral_congr_ae hJ)
