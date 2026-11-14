-- Prove2me | solution 1 for AvramDividend.Classical.avram_b35_original_finite_range_stopped_cash_initial_event_from_two_noise_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:21:40.795238+00:00
-- url     : https://prove2.me/submissions/29efb877-bb68-4f20-a9a6-596a2c048247

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b33_original_finite_range_initial_event_aggregate_centered_noise
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b21_initial_event_local_aggregate_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original physical stopped cash has its initial-event mean upper once the two-source Ito pathwise bound is established. -/
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
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (H : Ω → ℝ)
    (hHsource : ∀ ω, H ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (if τ ω = 0 ∨
              (τ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) :
    ∃ (R Jsmall : ℝ≥0 → Ω → ℝ) (M : Ω → ℝ),
      Integrable M P ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        let E : Set Ω := A ∩ {ω : Ω | τ ω ≠ 0}
        IntegrableOn H E P →
        (∀ᵐ ω ∂(P.restrict E), H ω ≤ w x + M ω) →
        (∫ ω in E, H ω ∂P) ≤ w x * (P E).toReal) ∧
      (∀ ω, M ω = R (τ ω) ω + Jsmall (τ ω) ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨M, R, Jsmall, hMI, hMzero, hRsource, hJsource, hMsource⟩ :=
    avram_b33_original_finite_range_initial_event_aggregate_centered_noise
      X hX hFinite n hn τ hτstop hτbound S hτrange
  refine ⟨R, Jsmall, M, hMI, ?_, hMsource⟩
  intro A hA
  dsimp only
  intro hHI hUpper
  let E : Set Ω := A ∩ {ω : Ω | τ ω ≠ 0}
  have hE : MeasurableSet[𝓕.rightCont 0] E :=
    hA.inter (avram_ubv_finite12_positive_clock_initial_measurable
      τ hτstop)
  have hZero : (∫ ω in E, M ω ∂P) = 0 := hMzero E hE
  have hUpper' : ∀ᵐ ω ∂(P.restrict E),
      H ω ≤ w x + M ω + (0 : ℝ) := by
    filter_upwards [hUpper] with ω hw
    simpa using hw
  have hb :=
    avram_b21_initial_event_local_aggregate_budget
      E hE (w x) H M (fun _ : Ω => (0 : ℝ))
      hHI hMI.integrableOn (integrable_const (0 : ℝ)).integrableOn
      hZero hUpper'
  simpa only [integral_zero, add_zero] using hb
