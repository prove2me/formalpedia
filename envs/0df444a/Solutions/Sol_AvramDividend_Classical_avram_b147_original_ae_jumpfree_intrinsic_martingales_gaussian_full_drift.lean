-- Prove2me | solution 1 for AvramDividend.Classical.avram_b147_original_ae_jumpfree_intrinsic_martingales_gaussian_full_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:47:03.860334+00:00
-- url     : https://prove2.me/submissions/40b13508-fdd8-4219-b7b1-2ed56bad0899

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
import Theorems.Thm_AvramDividend_Classical_avram_b146_original_ae_jumpfree_intrinsic_gaussian_full_drift_source_increment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Gaussian and compensated small-jump channels are genuine integrable same-filtration martingales, with the exact physical Gaussian-drift source increment on conull jumpfree random clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (s t : Ω → ℝ≥0) (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∃ (R Jsmall M : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
          atTop (𝓝 (R u ω))) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
          atTop (𝓝 (Jsmall u ω))) ∧
      (∀ u : ℝ≥0, Integrable (R u) P) ∧
      (∀ u : ℝ≥0, Integrable (Jsmall u) P) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (R b) ω = R a ω) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (Jsmall b) ω = Jsmall a ω) ∧
      (∀ u ω, X.X u ω = (u : ℝ) * X.c + M u ω + Jsmall u ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω) ∧
      (∀ᵐ ω ∂P, X.X (t ω) ω - X.X (s ω) ω =
        ((t ω : ℝ) - (s ω : ℝ)) *
          (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) +
        (R (t ω) ω - R (s ω) ω)) := by
  obtain ⟨R, Jsmall, MG, MJ, hRsrc, hJsrc, hRI, hRM, hJI, hJM,
      hMGI, hMJI, hMC, hJC, hMG, hMJ⟩ :=
    avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
      X hX hFinite n hn τ hτstop hτbound S hτrange
  obtain ⟨M, hFull, hJumpfree⟩ :=
    avram_b146_original_ae_jumpfree_intrinsic_gaussian_full_drift_source_increment
      X hFinite R Jsmall hRsrc hJsrc s t hOrder hNoJump
  exact ⟨R, Jsmall, M, hRsrc, hJsrc, hRI, hJI, hRM, hJM,
    hFull, hJumpfree⟩
