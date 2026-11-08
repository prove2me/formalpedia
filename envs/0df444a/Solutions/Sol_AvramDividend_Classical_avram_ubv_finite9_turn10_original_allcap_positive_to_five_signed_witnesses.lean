-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_turn10_original_allcap_positive_to_five_signed_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T23:48:32.226531+00:00
-- url     : https://prove2.me/submissions/c61958a4-ff50-4b43-b70e-a773bb80af84

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn10_positive_clock_allcap_five_signed_witnesses

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Lévy reward's positive-clock expected upper bound produces
the five signed HJB-budget witnesses without a finite-cap restriction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hpositive : ∀ k,
      (∫ ω in {ω : Ω | σ k ω ≠ 0}, F k ω ∂P) ≤
        w x * (P {ω : Ω | σ k ω ≠ 0}).toReal) :
    ∀ k, ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        (if σ k ω = 0 then w x else F k ω) ≤
          w x + Mc ω + Ms ω + Ml ω + G ω + R ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  exact avram_ubv_finite9_turn10_positive_clock_allcap_five_signed_witnesses
    (w x) (σ k) (F k)
    (avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
      𝓕 (σ k) (hσstop k))
    (hFI k) (hpositive k)
