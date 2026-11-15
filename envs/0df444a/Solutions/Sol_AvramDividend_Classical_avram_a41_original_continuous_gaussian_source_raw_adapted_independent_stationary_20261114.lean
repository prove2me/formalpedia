-- Prove2me | solution 1 for AvramDividend.Classical.avram_a41_original_continuous_gaussian_source_raw_adapted_independent_stationary_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:12:20.02298+00:00
-- url     : https://prove2.me/submissions/72ef1771-7a7c-4afa-96de-118fe96c8ddc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a39_original_gaussian_raw_adapted_zero_start_ae_continuous_representative_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_gaussian_limit_raw_filtration_indep_of_ae_rep_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_limit_increment_stationary_law_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) ∧
      (∀ s T : ℝ≥0, Indep
        (MeasurableSpace.comap
          (fun ω => G (s + T) ω - G s ω) inferInstance)
        (𝓕 s) P) ∧
      (∀ T, ∃ Z : Ω → ℝ, Measurable Z ∧
        ∀ s : ℝ≥0,
          Measure.map (fun ω => G (s + T) ω - G s ω) P =
          Measure.map Z P) := by
  obtain ⟨G, hAdapt, hZero, hEq, hCont⟩ :=
    avram_a39_original_gaussian_raw_adapted_zero_start_ae_continuous_representative_20261114
      X hFinite R hR
  have hInd :=
    avram_a27_original_gaussian_limit_raw_filtration_indep_of_ae_rep_20261114
      X hX hFinite R G hR hEq
  refine ⟨G, hAdapt, hZero, hEq, hCont, ?_, ?_⟩
  · intro s T
    exact hInd s (s + T)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ T from zero_le))
  · intro T
    obtain ⟨Z, hZ, hStatR⟩ :=
      avram_a24_original_gaussian_limit_increment_stationary_law_20261113
        X hX hFinite R hR T
    refine ⟨Z, hZ, ?_⟩
    intro s
    have hMapL :
        (fun ω => G (s + T) ω - G s ω) =ᵐ[P]
        (fun ω => R (s + T) ω - R s ω) := by
      filter_upwards [hEq] with ω hω
      rw [hω (s + T), hω s]
    calc
      Measure.map (fun ω => G (s + T) ω - G s ω) P =
        Measure.map (fun ω => R (s + T) ω - R s ω) P :=
          Measure.map_congr hMapL
      _ = Measure.map Z P := hStatR s
