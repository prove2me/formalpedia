-- Prove2me | solution 1 for AvramDividend.Classical.avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:26:06.589187+00:00
-- url     : https://prove2.me/submissions/d6d43a2d-3c19-4224-9029-3f2a6749905b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a41_original_continuous_gaussian_source_raw_adapted_independent_stationary_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a42_original_gaussian_alltime_ae_representative_inherits_martingale_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
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
          Measure.map Z P) ∧
      (∀ t : ℝ≥0, Integrable (G t) P ∧
        (∫ ω, G t ω ∂P) = 0) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (G t) ω = G s ω) := by
  obtain ⟨G, hAdapt, hZero, hEq, hCont, hInd, hStat⟩ :=
    avram_a41_original_continuous_gaussian_source_raw_adapted_independent_stationary_20261114
      X hX hFinite R hR
  obtain ⟨hGInt, hGMart⟩ :=
    avram_a42_original_gaussian_alltime_ae_representative_inherits_martingale_20261114
      X hX hFinite R G hR hEq
  have hRM := avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
      X hX hFinite R hR
  refine ⟨G, hAdapt, hZero, hEq, hCont, hInd, hStat, ?_, hGMart⟩
  intro t
  have hGt : (G t) =ᵐ[P] (R t) := by
    filter_upwards [hEq] with ω hω
    exact hω t
  refine ⟨hGInt t, ?_⟩
  calc
    (∫ ω, G t ω ∂P) = (∫ ω, R t ω ∂P) :=
      integral_congr_ae hGt
    _ = 0 := (hRM t).2
