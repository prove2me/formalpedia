-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_finite_range_positive_clock_two_fullmark_noises_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:51:18.801764+00:00
-- url     : https://prove2.me/submissions/07f0287a-4ec9-4aac-b566-c7b6effbbc07

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_finite_range_fullmark_two_stopped_noises_reward
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Both true physical stopped noises integrate to zero on the initially measurable positive-clock mask. -/
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
        ∂(dividendMeasure D ω)).toReal) :
    let μ : ℝ := ∫ ω, X.X 1 ω ∂P
    ∃ (R Jsmall Jfull : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (nhds (R t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) ∧
      Integrable (fun ω => R (τ ω) ω) P ∧
      Integrable (fun ω => Jfull (τ ω) ω) P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P
        (fun ω => R (τ ω) ω) ω = 0) ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P
        (fun ω => Jfull (τ ω) ω) ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω =
          Jsmall t ω + avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          (t : ℝ) * (X.c - μ)) ∧
      (∀ᵐ ω ∂P, F ω =
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + (τ ω : ℝ) * μ + R (τ ω) ω + Jfull (τ ω) ω -
            (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
             then rightLimit D (τ ω) ω else D (τ ω) ω)) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A ∩ {η : Ω | τ η ≠ 0}, R (τ ω) ω ∂P) = 0 ∧
        (∫ ω in A ∩ {η : Ω | τ η ≠ 0}, Jfull (τ ω) ω ∂P) = 0) := by
  obtain ⟨R, Jsmall, Jfull, hR, hJ, hRI, hJI, hRzero, hJzero,
    hFull, hReward⟩ :=
    avram_ja18_original_finite_range_fullmark_two_stopped_noises_reward
      X hX hFinite q x w D n hn τ hτstop hτbound S hτrange F hFsource
  refine ⟨R, Jsmall, Jfull, hR, hJ, hRI, hJI, hRzero,
    hJzero, hFull, hReward, ?_⟩
  intro A hA
  have hPositive : MeasurableSet[𝓕.rightCont 0] {ω : Ω | τ ω ≠ 0} :=
    avram_ubv_finite12_positive_clock_initial_measurable τ hτstop
  have hE : MeasurableSet[𝓕.rightCont 0] (A ∩ {ω : Ω | τ ω ≠ 0}) :=
    hA.inter hPositive
  constructor
  · exact avram_ubv_jump11_past_event_integral_of_condexp_zero
      (𝓕.rightCont 0) (𝓕.rightCont.le 0)
      (fun ω => R (τ ω) ω) hRI hRzero _ hE
  · exact avram_ubv_jump11_past_event_integral_of_condexp_zero
      (𝓕.rightCont 0) (𝓕.rightCont.le 0)
      (fun ω => Jfull (τ ω) ω) hJI hJzero _ hE
