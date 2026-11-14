-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_limit_gaussian_positive_time_square_moment_20261113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:56:42.302106+00:00
-- url     : https://prove2.me/submissions/9cda52bb-f837-46e7-9769-275b76c385ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
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

/-- Gaussian-limit positive-time variance follows from an actual same-source zero-jump companion. -/
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
  intro t ht
  obtain ⟨Jsmall, hJsource, _, _⟩ :=
    avram_ja18e_original_smallband_locally_uniform_cadlag_limit X hX hFinite
  obtain ⟨Y, hYν, hYσ, hDecomp⟩ :=
    avram_ja19_original_zero_nu_process_from_finite_jump_source
      X hX hFinite Jsmall hJsource
  have hJt : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)) := by
    filter_upwards [hJsource] with ω hω
    exact hω t
  have hRt : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)) := by
    filter_upwards [hR] with ω hω
    exact hω t
  have hDt : ∀ᵐ ω ∂P,
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω := by
    filter_upwards [hDecomp] with ω hω
    exact hω t
  have hEq :=
    avram_a21_original_gaussian_limit_identified_with_same_source_zero_nu_process_20261113
      X Y Jsmall R t hJt hRt hDt
  have hYSq :=
    avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
      Y hYν t
  have hSq : (fun ω => (R t ω) ^ 2) =ᵐ[P]
      (fun ω => (Y.X t ω - (t : ℝ) * Y.c) ^ 2) := by
    filter_upwards [hEq] with ω hω
    rw [hω]
  have hInt : Integrable (fun ω => (R t ω) ^ 2) P :=
    hYSq.1.congr hSq.symm
  have hMoment : (∫ ω, (R t ω) ^ 2 ∂P) =
      (t : ℝ) * X.σ ^ 2 := calc
    (∫ ω, (R t ω) ^ 2 ∂P) =
        (∫ ω, (Y.X t ω - (t : ℝ) * Y.c) ^ 2 ∂P) :=
      integral_congr_ae hSq
    _ = (t : ℝ) * Y.σ ^ 2 := hYSq.2
    _ = (t : ℝ) * X.σ ^ 2 := by rw [hYσ]
  exact ⟨hInt, hMoment⟩
