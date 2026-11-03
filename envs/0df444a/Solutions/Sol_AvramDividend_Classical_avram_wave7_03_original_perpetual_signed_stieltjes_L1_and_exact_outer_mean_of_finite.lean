-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:44:37.006857+00:00
-- url     : https://prove2.me/submissions/f7048271-f3af-4824-8c60-d78baa1f9172

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Exact full original Lévy dividend signed Stieltjes mean: under
    finite canonical expectation the complete unrestricted signed integral
    is genuinely L1 on P and recovers the double ENNReal dividendValue. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let g : Ω → ℝ := fun ω =>
    ∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
  have hFm : Measurable F :=
    avram_wave6_08_original_perpetual_stieltjes_cash_measurable
      X x D hD q
  have hValueLin : (∫⁻ ω, F ω ∂P) < ⊤ := by
    simpa only [dividendValue, F] using hFinite
  have hAeFin : ∀ᵐ ω ∂P, F ω < ⊤ :=
    ae_lt_top hFm (ne_of_lt hValueLin)
  have hFMean :=
    avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
      X x D hD q hFinite
  have hEq : (fun ω => (F ω).toReal) =ᵐ[P] g := by
    filter_upwards [hAeFin] with ω hω
    have hPath :=
      avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
        X x D hD ω q hω
    have hgNN : 0 ≤ g ω := by
      apply integral_nonneg
      intro t
      exact (Real.exp_pos (-(q * t))).le
    calc
      (F ω).toReal = (ENNReal.ofReal (g ω)).toReal :=
        congrArg ENNReal.toReal hPath.2.symm
      _ = g ω := ENNReal.toReal_ofReal hgNN
  have hGInt : Integrable g P := hFMean.1.congr hEq
  constructor
  · exact hGInt
  · calc
      dividendValue X q x D =
        ENNReal.ofReal (∫ ω, (F ω).toReal ∂P) := hFMean.2
      _ = ENNReal.ofReal (∫ ω, g ω ∂P) :=
        congrArg ENNReal.ofReal (integral_congr_ae hEq)
