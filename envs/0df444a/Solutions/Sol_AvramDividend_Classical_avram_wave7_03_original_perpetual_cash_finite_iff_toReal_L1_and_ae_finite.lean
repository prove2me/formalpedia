-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_perpetual_cash_finite_iff_toReal_L1_and_ae_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:54:07.389306+00:00
-- url     : https://prove2.me/submissions/ce8d228b-1c5a-4daa-bf61-8f444d4b7c4d

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Exact original perpetual cash finiteness criterion. Real conversion is
    L1 precisely with genuine almost-sure finiteness of the source cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ) :
    (dividendValue X q x D < ⊤) ↔
      Integrable (fun ω : Ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P ∧
      (∀ᵐ ω ∂P, (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤) := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hMeas : Measurable F :=
    avram_wave6_08_original_perpetual_stieltjes_cash_measurable
      X x D hD q
  constructor
  · intro hFinite
    have hInt :=
      (avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
        X x D hD q hFinite).1
    have hLin : (∫⁻ ω, F ω ∂P) < ⊤ := by
      simpa only [dividendValue, F] using hFinite
    have hAeFin : ∀ᵐ ω ∂P, F ω < ⊤ :=
      ae_lt_top hMeas (ne_of_lt hLin)
    exact ⟨hInt, hAeFin⟩
  · rintro ⟨hInt, hAeFin⟩
    have hNN : ∀ᵐ ω ∂P, 0 ≤ (F ω).toReal :=
      Filter.Eventually.of_forall (fun ω => ENNReal.toReal_nonneg)
    have hCashEq : (∫⁻ ω, F ω ∂P) =
        ∫⁻ ω, ENNReal.ofReal ((F ω).toReal) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hAeFin] with ω hω
      exact (ENNReal.ofReal_toReal (ne_of_lt hω)).symm
    have hIdentity : dividendValue X q x D =
        ENNReal.ofReal (∫ ω, (F ω).toReal ∂P) := by
      change (∫⁻ ω, F ω ∂P) =
        ENNReal.ofReal (∫ ω, (F ω).toReal ∂P)
      calc
        (∫⁻ ω, F ω ∂P) =
          ∫⁻ ω, ENNReal.ofReal ((F ω).toReal) ∂P := hCashEq
        _ = ENNReal.ofReal (∫ ω, (F ω).toReal ∂P) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hNN).symm
    rw [hIdentity]
    exact ENNReal.ofReal_lt_top
