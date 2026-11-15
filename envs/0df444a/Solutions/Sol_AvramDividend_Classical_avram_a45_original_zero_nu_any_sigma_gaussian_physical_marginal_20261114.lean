-- Prove2me | solution 1 for AvramDividend.Classical.avram_a45_original_zero_nu_any_sigma_gaussian_physical_marginal_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:32:58.504464+00:00
-- url     : https://prove2.me/submissions/d1a2619c-cb1c-46fc-b93b-2aa3ead02ae5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a44_original_zero_nu_positive_sigma_gaussian_physical_marginal_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hNu : X.ν = 0)
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
  have hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤ := by simp [hNu]
  by_cases hSigma : X.σ = 0
  · have hZero :=
      avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
        X hX hFinite R hR hSigma
    intro t
    have hEq : (R t) =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
      filter_upwards [hZero] with ω hω
      exact hω t
    have hMap : Measure.map (R t) P = gaussianReal 0 0 := by
      calc
        Measure.map (R t) P = Measure.map (fun _ : Ω => (0 : ℝ)) P :=
          Measure.map_congr hEq
        _ = Measure.dirac 0 := by simp
        _ = gaussianReal 0 0 := (gaussianReal_zero_var 0).symm
    simpa [hSigma] using hMap
  · have hPos : 0 < X.σ :=
      lt_of_le_of_ne X.σ_nonneg (Ne.symm hSigma)
    exact avram_a44_original_zero_nu_positive_sigma_gaussian_physical_marginal_20261114
      X hNu hPos R hR
