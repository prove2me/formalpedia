-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb20_original_gaussian_finite_range_stop_condexp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:26:17.011984+00:00
-- url     : https://prove2.me/submissions/574b07c2-b8b7-4bee-9613-097c674042b8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18_finite_range_optional_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original intrinsic Gaussian residual has centred integrable values
at finite-valued bounded stopping clocks, without a replacement Levy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτbound : ∀ ω, τ ω ≤ T)
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S) :
    Integrable (fun ω => R (τ ω) ω) P ∧
    (∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P
        (fun ω => R (τ ω) ω) ω = 0) := by
  have hRzero : ∀ᵐ ω ∂P, R 0 ω = 0 := by
    filter_upwards [hRsource] with ω hω
    have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
        (nhds (R 0 ω)) := by
      simpa only [
        avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin
      ] using hω 0
    exact tendsto_nhds_unique h0 tendsto_const_nhds
  exact avram_ja18_finite_range_optional_condexp_zero
    R τ T hτstop hτbound S hτrange hRint hRmart hRzero
