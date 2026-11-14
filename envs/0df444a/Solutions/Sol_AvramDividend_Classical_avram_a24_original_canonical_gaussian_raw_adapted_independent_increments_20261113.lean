-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_canonical_gaussian_raw_adapted_independent_increments_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:07:11.016099+00:00
-- url     : https://prove2.me/submissions/e5b83fe0-6763-439b-8be7-07f891025886

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_gaussian_limit_original_past_independent_rep_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a24_indep_comap_ae_equal_measurable_source_v2_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- One canonical original-filtration adapted Gaussian residual source has genuinely independent increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) ∧
      (∀ s T : ℝ≥0, Indep
        (MeasurableSpace.comap (fun ω => G (s + T) ω - G s ω) inferInstance)
        (𝓕 s) P) := by
  obtain ⟨G, hAdapt, hZero, hG⟩ :=
    avram_a24_original_gaussian_adapted_zero_origin_20261113 X R hR
  letI : IsProbabilityMeasure P := X.isProbability
  refine ⟨G, hAdapt, hZero, hG, ?_⟩
  intro s T
  obtain ⟨D, hDMeas, hDIndep, hDae⟩ :=
    avram_a24_uniform_gaussian_limit_original_past_independent_rep_20261113
      X hX hFinite R hR T
  have hEq : (D s) =ᵐ[P] (fun ω => G (s + T) ω - G s ω) := by
    filter_upwards [hDae, hG] with ω hDω hGω
    rw [hDω s, hGω (s + T), hGω s]
  have hRaw : Indep
      (MeasurableSpace.comap (D s) inferInstance) (𝓕 s) P :=
    indep_of_indep_of_le_right (hDIndep s) (𝓕.le_rightCont s)
  have hMeas : Measurable (fun ω => G (s + T) ω - G s ω) :=
    ((hAdapt (s + T)).mono (𝓕.le (s + T)) le_rfl).sub
      ((hAdapt s).mono (𝓕.le s) le_rfl)
  exact avram_a24_indep_comap_ae_equal_measurable_source_v2_20261114
    (𝓕 s) (𝓕.le s) (D s)
    (fun ω => G (s + T) ω - G s ω)
    (hDMeas s) hMeas hEq hRaw
