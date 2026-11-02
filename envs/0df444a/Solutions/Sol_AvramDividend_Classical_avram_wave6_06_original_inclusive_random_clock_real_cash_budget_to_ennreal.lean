-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_inclusive_random_clock_real_cash_budget_to_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:16:20.614776+00:00
-- url     : https://prove2.me/submissions/fa17d8ea-bb17-49e9-bef4-e7a92dee0ef2

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Convert the exact original closed random-clock Stieltjes cash, including
the terminal right-payment atom, from an integrable real budget to ENNReal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hCashFinite : ∀ᵐ ω ∂P,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤)
    (hCashI : Integrable Cash P)
    (B : ℝ) (hBudget : (∫ ω, Cash ω ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal B := by
  have hCashNonneg : 0 ≤ᵐ[P] Cash := by
    filter_upwards [] with ω
    rw [hCash ω]
    exact ENNReal.toReal_nonneg
  have hCashSource :
      (fun ω => ENNReal.ofReal (Cash ω)) =ᵐ[P]
        (fun ω => ∫⁻ s in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by
    filter_upwards [hCashFinite] with ω hFinite
    rw [hCash ω]
    exact ENNReal.ofReal_toReal (ne_of_lt hFinite)
  calc
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) =
      (∫⁻ ω, ENNReal.ofReal (Cash ω) ∂P) :=
        (lintegral_congr_ae hCashSource).symm
    _ = ENNReal.ofReal (∫ ω, Cash ω ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hCashI hCashNonneg).symm
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hBudget
