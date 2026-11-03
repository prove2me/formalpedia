-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_signed_stieltjes_expected_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:40:50.491204+00:00
-- url     : https://prove2.me/submissions/2e402f5b-4671-4e28-bc9f-9593e2da210f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_random_clock_full_ennreal_cash_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_signed_stieltjes_mean_nonneg
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Genuine expected signed Stieltjes cash is monotone in two
    ordered bounded measurable random clocks of the original process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ σ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hσBound : ∀ ω, σ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hσMeas : Measurable (fun ω => (σ ω : ℝ)))
    (hClock : ∀ ω, τ ω ≤ σ ω) :
    (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤
    (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hENN :=
    avram_wave7_03_original_random_clock_full_ennreal_cash_monotone
      X x D hDiv q τ σ hClock
  have hEqτ :=
    avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
      X x C D hD q hq T τ hτBound hτMeas
  have hEqσ :=
    avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
      X x C D hD q hq T σ hσBound hσMeas
  have hτNonneg :=
    avram_wave7_03_original_bounded_random_clock_signed_stieltjes_mean_nonneg
      X x C D hD q hq T τ hτBound hτMeas
  have hσNonneg :=
    avram_wave7_03_original_bounded_random_clock_signed_stieltjes_mean_nonneg
      X x C D hD q hq T σ hσBound hσMeas
  have hOfRealLe : ENNReal.ofReal
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤
      ENNReal.ofReal
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
    calc
      _ = (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) := hEqτ.symm
      _ ≤ (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) := hENN
      _ = _ := hEqσ
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hOfRealLe
  simpa only [ENNReal.toReal_ofReal hτNonneg,
    ENNReal.toReal_ofReal hσNonneg] using hReal
