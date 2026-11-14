-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:19:39.689761+00:00
-- url     : https://prove2.me/submissions/1f8f06de-0b43-4923-aa27-537a8802ed59
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18e_original_smallband_locally_uniform_cadlag_limit
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_zero_nu_process_from_finite_jump_source
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_gaussian_fixed_time_integrable_centered_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_identified_with_same_source_zero_nu_process_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Physical Gaussian-limit source mean zero follows from its same-source zero-jump companion. -/
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
    ∀ t : ℝ≥0,
      Integrable (R t) P ∧
      (∫ ω, R t ω ∂P) = 0 := by
  intro t
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
  have hYmean :=
    avram_a21_original_zero_jump_gaussian_fixed_time_integrable_centered_20261113
      Y hYν t
  have hYeq : (fun ω => R t ω) =ᵐ[P]
      (fun ω => Y.X t ω - (t : ℝ) * Y.c) := hEq
  have hInt : Integrable (R t) P :=
    hYmean.1.congr hYeq.symm
  have hMean : (∫ ω, R t ω ∂P) = 0 := calc
    (∫ ω, R t ω ∂P) =
      (∫ ω, Y.X t ω - (t : ℝ) * Y.c ∂P) :=
      integral_congr_ae hYeq
    _ = 0 := hYmean.2
  exact ⟨hInt, hMean⟩
