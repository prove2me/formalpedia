-- Prove2me | solution 2 for AvramDividend.Classical.avram_a21_original_limit_gaussian_positive_time_square_moment_20261113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:45:35.238556+00:00
-- url     : https://prove2.me/submissions/00f79baa-561e-4ccb-b303-069f987fc966
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18e_original_smallband_locally_uniform_cadlag_limit
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_zero_nu_process_from_finite_jump_source
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_identified_with_same_source_zero_nu_process_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original-space Gaussian identification transfers the exact zero-jump square moment to the intrinsic limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ t : ℝ≥0, 0 < t →
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 := by
  obtain ⟨Jsmall, hJ, _, _⟩ :=
    avram_ja18e_original_smallband_locally_uniform_cadlag_limit
      X hX hFinite
  obtain ⟨Y, hNu, hSigma, hDecomp⟩ :=
    avram_ja19_original_zero_nu_process_from_finite_jump_source
      X hX hFinite Jsmall hJ
  intro t _ht
  have hJt : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)) := by
    filter_upwards [hJ] with ω hω
    exact hω t
  have hRt : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)) := by
    filter_upwards [hR] with ω hω
    exact hω t
  have hDecompT : ∀ᵐ ω ∂P,
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω := by
    filter_upwards [hDecomp] with ω hω
    exact hω t
  have hEq :=
    avram_a21_original_gaussian_limit_identified_with_same_source_zero_nu_process_20261113
      X Y Jsmall R t hJt hRt hDecompT
  have hSq : ∀ᵐ ω ∂P, (R t ω) ^ 2 =
      (Y.X t ω - (t : ℝ) * Y.c) ^ 2 := by
    filter_upwards [hEq] with ω hω
    rw [hω]
  have hMom :=
    avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
      Y hNu t
  constructor
  · have hSqRev : ∀ᵐ ω ∂P,
        (Y.X t ω - (t : ℝ) * Y.c) ^ 2 = (R t ω) ^ 2 := by
      filter_upwards [hSq] with ω hω
      exact hω.symm
    exact hMom.1.congr hSqRev
  · calc
      (∫ ω, (R t ω) ^ 2 ∂P) =
          (∫ ω, (Y.X t ω - (t : ℝ) * Y.c) ^ 2 ∂P) :=
        integral_congr_ae hSq
      _ = (t : ℝ) * Y.σ ^ 2 := hMom.2
      _ = (t : ℝ) * X.σ ^ 2 := by rw [hSigma]
