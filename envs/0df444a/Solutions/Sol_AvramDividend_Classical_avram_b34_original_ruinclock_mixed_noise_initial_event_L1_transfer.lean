-- Prove2me | solution 1 for AvramDividend.Classical.avram_b34_original_ruinclock_mixed_noise_initial_event_L1_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:36:26.938193+00:00
-- url     : https://prove2.me/submissions/6e3c98a9-9824-4e03-bea3-8ed7e325393d

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_restricted_L1_limit_preserves_zero_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Restricted L1 convergence carries the genuine original mixed source noise centring to a random ruin-clipped clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω)))
    (κ : Ω → ℝ≥0)
    (τ : ℕ → Ω → ℝ≥0)
    (hκstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (κ ω : WithTop ℝ≥0)))
    (hτstop : ∀ m, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ m ω : WithTop ℝ≥0)))
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    (∀ m, Integrable
      (fun ω => R (τ m ω) ω + Jsmall (τ m ω) ω) P) →
    Integrable (fun ω => R (κ ω) ω + Jsmall (κ ω) ω) P →
    (∀ m, (∫ ω in A,
      R (τ m ω) ω + Jsmall (τ m ω) ω ∂P) = 0) →
    Tendsto
      (fun m => ∫⁻ ω in A,
        ‖(R (τ m ω) ω + Jsmall (τ m ω) ω) -
          (R (κ ω) ω + Jsmall (κ ω) ω)‖ₑ ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)) →
    (∫ ω in A, R (κ ω) ω + Jsmall (κ ω) ω ∂P) = 0 := by
  intro hInt hFinalInt hZero hL1
  have hAm : MeasurableSet A := (𝓕.rightCont.le 0) A hA
  exact avram_gaussian12_restricted_L1_limit_preserves_zero_mean
    A hAm
    (fun m ω => R (τ m ω) ω + Jsmall (τ m ω) ω)
    hInt
    (fun ω => R (κ ω) ω + Jsmall (κ ω) ω)
    hFinalInt hZero hL1
