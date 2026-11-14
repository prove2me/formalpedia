-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_gaussian_raw_adapted_indep_stationary_process_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:43:11.963376+00:00
-- url     : https://prove2.me/submissions/001333b5-65dd-4b70-8455-a04ed6bb46aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_limit_increment_stationary_law_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_gaussian_limit_raw_filtration_indep_of_ae_rep_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original raw-adapted Gaussian source has both source-past independent and stationary increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        Indep (MeasurableSpace.comap
          (fun ω => G t ω - G s ω) inferInstance) (𝓕 s) P) ∧
      (∀ s T : ℝ≥0,
        Measure.map (fun ω => G (s + T) ω - G s ω) P =
        Measure.map (G T) P) := by
  obtain ⟨R, hLimit, _, _, _⟩ :=
    avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
      X hX hFinite
  have hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)) := by
    filter_upwards [hLimit] with ω hω
    exact hω.1
  obtain ⟨G, hAdapt, hZero, hEq⟩ :=
    avram_a24_original_gaussian_adapted_zero_origin_20261113 X R hR
  refine ⟨G, hAdapt, hZero, ?_, ?_⟩
  · exact avram_a27_original_gaussian_limit_raw_filtration_indep_of_ae_rep_20261114
      X hX hFinite R G hR hEq
  ·
    intro s T
    obtain ⟨Z, _, hStatR⟩ :=
      avram_a24_original_gaussian_limit_increment_stationary_law_20261113
        X hX hFinite R hR T
    have hMapL : (fun ω => G (s + T) ω - G s ω) =ᵐ[P]
        (fun ω => R (s + T) ω - R s ω) := by
      filter_upwards [hEq] with ω hω
      rw [hω (s + T), hω s]
    have hMap0 : (fun ω => R (0 + T) ω - R 0 ω) =ᵐ[P]
        (R T) := by
      filter_upwards [hEq] with ω hω
      have h0 : R 0 ω = 0 := by
        rw [← hω 0, hZero ω]
      simp [h0]
    have hMapR : (R T) =ᵐ[P] (G T) := by
      filter_upwards [hEq] with ω hω
      exact (hω T).symm
    calc
      Measure.map (fun ω => G (s + T) ω - G s ω) P =
        Measure.map (fun ω => R (s + T) ω - R s ω) P :=
          Measure.map_congr hMapL
      _ = Measure.map Z P := hStatR s
      _ = Measure.map (fun ω => R (0 + T) ω - R 0 ω) P :=
          (hStatR 0).symm
      _ = Measure.map (R T) P := Measure.map_congr hMap0
      _ = Measure.map (G T) P := Measure.map_congr hMapR
