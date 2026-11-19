-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_finite_range_fullmark_signed_ito_initial_event_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:50:45.599123+00:00
-- url     : https://prove2.me/submissions/0e96d28d-4cb0-4974-b090-58a7d0dd418e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb19_two_noise_initial_event_masked_reward_budget
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_finite_range_fullmark_two_stopped_noises_reward
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- The actual fullmark stopped source turns the signed cash inequality into an event budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (E T : Set Ω) (hE : MeasurableSet[𝓕.rightCont 0] E)
    (hET : E ⊆ T) (b : ℝ) (hb : 0 ≤ b)
    (hIto : ∀ (R Jsmall Jfull : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (nhds (R t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω =
          Jsmall t ω + avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          (t : ℝ) * (X.c - ∫ ω, X.X 1 ω ∂P)) →
      ∃ B : Ω → ℝ,
        (∀ᵐ ω ∂(P.restrict E), B ω ≤ 0) ∧
        (∀ᵐ ω ∂(P.restrict E),
          F ω ≤ b + R (τ ω) ω + Jfull (τ ω) ω + B ω)) :
    (∫ ω in E, F ω ∂P) ≤ b * (P T).toReal := by
  obtain ⟨R, Jsmall, Jfull, hR, hJ, hRI, hJI, hRzero, hJzero,
    hFull, hReward⟩ :=
    avram_ja18_original_finite_range_fullmark_two_stopped_noises_reward
      X hX hFinite q x w D n hn τ hτstop hτbound S hτrange F hFsource
  obtain ⟨B, hB, hLedger⟩ := hIto R Jsmall Jfull hR hJ hFull
  exact avram_jb19_two_noise_initial_event_masked_reward_budget
    (𝓕.rightCont 0) (𝓕.rightCont.le 0)
    E T hE hET b hb F
    (fun ω => R (τ ω) ω) (fun ω => Jfull (τ ω) ω)
    B hFI hRI hJI hRzero hJzero hB hLedger
