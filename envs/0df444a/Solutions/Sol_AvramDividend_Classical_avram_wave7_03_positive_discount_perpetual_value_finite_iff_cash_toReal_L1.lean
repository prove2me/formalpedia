-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_positive_discount_perpetual_value_finite_iff_cash_toReal_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:58:19.509933+00:00
-- url     : https://prove2.me/submissions/966a4dd2-f435-4b9c-8882-cb8b09ad9839

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- With positive discount, genuine original pathwise perpetual cash
    is finite a.e.; expected finiteness is exactly real-converted L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    (dividendValue X q x D < ⊤) ↔
      Integrable (fun ω : Ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hAeFin : ∀ᵐ ω ∂P, F ω < ⊤ :=
    avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
      X x C D hD q hq
  constructor
  · intro hFinite
    exact (avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
      X x D hD.1.1 q hFinite).1
  · intro hInt
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
