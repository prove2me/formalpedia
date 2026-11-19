-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_finite_range_positive_clock_fullmark_upper_implies_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:59:00.443487+00:00
-- url     : https://prove2.me/submissions/deb216bb-8e5a-4e43-bc75-0fa8aed7026d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_finite_range_positive_clock_two_fullmark_noises_centered
import Theorems.Thm_AvramDividend_Classical_avram_b21_initial_event_local_aggregate_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Physical fullmark centred stopped gains cancel on the initial positive-clock event. -/
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
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
    (hSigned : ∀ (R Jsmall Jfull : ℝ≥0 → Ω → ℝ),
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
      ∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | τ η ≠ 0})),
        F ω ≤ w x + R (τ ω) ω + Jfull (τ ω) ω) :
    (∫ ω in A ∩ {η : Ω | τ η ≠ 0}, F ω ∂P) ≤
      w x * (P (A ∩ {η : Ω | τ η ≠ 0})).toReal := by
  obtain ⟨R, Jsmall, Jfull, hR, hJ, hRI, hJI, hRzero, hJzero,
    hFull, hReward, hMasked⟩ :=
    avram_ja18_original_finite_range_positive_clock_two_fullmark_noises_centered
      X hX hFinite q x w D n hn τ hτstop hτbound S hτrange F hFsource
  have hE : MeasurableSet[𝓕.rightCont 0]
      (A ∩ {η : Ω | τ η ≠ 0}) :=
    hA.inter (avram_ubv_finite12_positive_clock_initial_measurable τ hτstop)
  have hMaskedZero := hMasked A hA
  have hM : Integrable (fun ω => R (τ ω) ω + Jfull (τ ω) ω) P :=
    hRI.add hJI
  have hMzero : (∫ ω in A ∩ {η : Ω | τ η ≠ 0},
      R (τ ω) ω + Jfull (τ ω) ω ∂P) = 0 := by
    rw [integral_add hRI.integrableOn hJI.integrableOn,
      hMaskedZero.1, hMaskedZero.2]
    ring
  have hUpper := hSigned R Jsmall Jfull hR hJ hFull
  have hUpper' :
      ∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | τ η ≠ 0})),
        F ω ≤ w x + (R (τ ω) ω + Jfull (τ ω) ω) + 0 := by
    filter_upwards [hUpper] with ω hω
    linarith
  have hBudget := avram_b21_initial_event_local_aggregate_budget
    (A ∩ {η : Ω | τ η ≠ 0}) hE (w x) F
    (fun ω => R (τ ω) ω + Jfull (τ ω) ω)
    (fun _ => (0 : ℝ))
    hFI.integrableOn hM.integrableOn (by simp)
    hMzero hUpper'
  simpa only [integral_zero, add_zero] using hBudget
