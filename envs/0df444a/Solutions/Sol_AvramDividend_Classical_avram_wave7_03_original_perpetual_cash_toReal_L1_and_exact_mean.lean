-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:38:31.93521+00:00
-- url     : https://prove2.me/submissions/2c80058f-bcff-4a39-88c2-662347352447

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section


/-- The full original perpetual Stieltjes cash is genuinely L1 whenever
    its canonical ENNReal expectation is finite, and conversion to the
    real mean is exact, with no time truncation or process replacement. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω : Ω,
          (∫⁻ t in paymentTimes (ruinTime X x D ω),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hMeas : Measurable F :=
    avram_wave6_08_original_perpetual_stieltjes_cash_measurable
      X x D hD q
  have hFin : (∫⁻ ω, F ω ∂P) < ⊤ := by
    simpa only [dividendValue, F] using hFinite
  have hInt : Integrable (fun ω => (F ω).toReal) P :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top
      hMeas.aemeasurable (ne_of_lt hFin)
  have hAeFin : ∀ᵐ ω ∂P, F ω < ⊤ :=
    ae_lt_top hMeas (ne_of_lt hFin)
  have hNN : ∀ᵐ ω ∂P, 0 ≤ (F ω).toReal :=
    Filter.Eventually.of_forall (fun ω => ENNReal.toReal_nonneg)
  have hEq : (∫⁻ ω, F ω ∂P) =
      ∫⁻ ω, ENNReal.ofReal ((F ω).toReal) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hAeFin] with ω hω
    exact (ENNReal.ofReal_toReal (ne_of_lt hω)).symm
  constructor
  · exact hInt
  · change (∫⁻ ω, F ω ∂P) =
      ENNReal.ofReal (∫ ω, (F ω).toReal ∂P)
    calc
      (∫⁻ ω, F ω ∂P) =
        ∫⁻ ω, ENNReal.ofReal ((F ω).toReal) ∂P := hEq
      _ = ENNReal.ofReal (∫ ω, (F ω).toReal ∂P) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hNN).symm
