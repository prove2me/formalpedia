-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_bounded_clock_stopped_residual_to_ennreal_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:46:42.615166+00:00
-- url     : https://prove2.me/submissions/a062b472-07cf-46e2-9bea-a49274786f5c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_toReal_budget_to_ennreal_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A stopped original Ito residual with centred martingale and
    negative drift controls the true dividend cash without integrable Term. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (B : ℝ) (Cash Term M G H : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hMI : Integrable M P)
    (hMZero : (∫ ω, M ω ∂P) = 0)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hGHNonpos : ∀ᵐ ω ∂P, G ω + H ω ≤ 0)
    (hResidual : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ B + M ω + G ω + H ω) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by
  letI : IsProbabilityMeasure P := X.isProbability
  apply avram_wave7_03_original_bounded_random_clock_toReal_budget_to_ennreal_cash
    X x C D hD q hq T τ hτBound hτMeas B
  have hPoint : Cash ≤ᵐ[P] (fun ω => B + M ω) := by
    filter_upwards [hTermNonneg, hGHNonpos, hResidual] with ω ht hg hr
    linarith only [ht, hg, hr]
  have hMI' : Integrable (fun ω => B + M ω) P :=
    (integrable_const B).add hMI
  have hMeanLe := integral_mono_ae hCashI hMI' hPoint
  have hMeanEq : (∫ ω, B + M ω ∂P) = B := by
    rw [integral_add (integrable_const B) hMI]
    simp [hMZero]
  calc
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal ∂P) =
        (∫ ω, Cash ω ∂P) := by simp only [← hCash]
    _ ≤ (∫ ω, B + M ω ∂P) := hMeanLe
    _ = B := hMeanEq
