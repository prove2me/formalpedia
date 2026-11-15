-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_positive_sigma_nonzero_nu_intrinsic_true_same_filtration_gaussian_companion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:29:09.421187+00:00
-- url     : https://prove2.me/submissions/c778802c-a61d-424c-bf81-5d3d9e12a44c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a28_original_intrinsic_gaussian_raw_allpath_cadlag_regularity
import Theorems.Thm_AvramDividend_Classical_avram_a28_original_intrinsic_gaussian_exact_zero_nu_laplace_exponent
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_gaussian_limit_raw_filtration_indep_of_ae_rep_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_limit_increment_stationary_law_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_gaussian_levy_assembly_from_path_independence_exponent_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source companion follows exactly from constructive all-path regularity and original Gaussian Laplace law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hSigmaPositive : 0 < X.σ) (hNuNonzero : X.ν ≠ 0) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        R t ω = Y.X t ω - (t : ℝ) * Y.c) := by
  obtain ⟨G, hAdapt, hZero, hEq, hRight, hLeft, hNoPos⟩ :=
    avram_a28_original_intrinsic_gaussian_raw_allpath_cadlag_regularity
      X hX hFinite R hR
  have hInd :=
    avram_a27_original_gaussian_limit_raw_filtration_indep_of_ae_rep_20261114
      X hX hFinite R G hR hEq
  have hLaw (s T : ℝ≥0) :
      Measure.map (fun ω => G (s + T) ω - G s ω) P =
      Measure.map (G T) P := by
    obtain ⟨Z, _, hStatR⟩ :=
      avram_a24_original_gaussian_limit_increment_stationary_law_20261113
        X hX hFinite R hR T
    have hL : (fun ω => G (s + T) ω - G s ω) =ᵐ[P]
        (fun ω => R (s + T) ω - R s ω) := by
      filter_upwards [hEq] with ω hω
      rw [hω (s + T), hω s]
    have h0 : (fun ω => R (0 + T) ω - R 0 ω) =ᵐ[P]
        (R T) := by
      filter_upwards [hEq] with ω hω
      have hz : R 0 ω = 0 := by rw [← hω 0, hZero ω]
      simp [hz]
    have hT : (R T) =ᵐ[P] (G T) := by
      filter_upwards [hEq] with ω hω
      exact (hω T).symm
    calc
      Measure.map (fun ω => G (s + T) ω - G s ω) P =
        Measure.map (fun ω => R (s + T) ω - R s ω) P :=
          Measure.map_congr hL
      _ = Measure.map Z P := hStatR s
      _ = Measure.map (fun ω => R (0 + T) ω - R 0 ω) P :=
          (hStatR 0).symm
      _ = Measure.map (R T) P := Measure.map_congr h0
      _ = Measure.map (G T) P := Measure.map_congr hT
  have hLap :=
    avram_a28_original_intrinsic_gaussian_exact_zero_nu_laplace_exponent
      X hX hFinite R hR G hEq
  obtain ⟨Y, hNu, hSigma, hC, hYX⟩ :=
    avram_a26_original_gaussian_levy_assembly_from_path_independence_exponent_20261114
      X G hAdapt hZero hRight hLeft hNoPos hInd hLaw hLap
  refine ⟨Y, hNu, hSigma, ?_⟩
  filter_upwards [hEq] with ω hGω
  intro t
  simpa only [hYX, hC, mul_zero, sub_zero] using (hGω t).symm
