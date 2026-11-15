-- Prove2me | solution 1 for AvramDividend.Classical.avram_a46_original_finiteactivity_zero_sigma_gaussian_residual_dirac_law_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:33:47.386106+00:00
-- url     : https://prove2.me/submissions/2fd4d5bb-170e-40f0-8880-cc5283ed29a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
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
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSigma : X.σ = 0)
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
  have hZero :=
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
