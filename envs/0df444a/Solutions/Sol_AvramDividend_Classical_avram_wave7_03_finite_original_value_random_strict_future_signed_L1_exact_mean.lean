-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_finite_original_value_random_strict_future_signed_L1_exact_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:21:06.403384+00:00
-- url     : https://prove2.me/submissions/6da4b683-c530-4e79-a72f-b6cbc2ff0043

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_future_random_clock_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_expected_random_strict_future_cash_le_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (T : Ω → ℝ) (hTm : Measurable T)
    (hFinite : dividendValue X q x D < ⊤) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let g : Ω → ℝ := fun ω =>
    ∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
  have hFMeas : Measurable F :=
    avram_wave7_03_original_strict_future_random_clock_cash_measurable X x D hD q T hTm
  have hFin : (∫⁻ ω, F ω ∂P) < ⊤ :=
    lt_of_le_of_lt
      (avram_wave7_03_original_expected_random_strict_future_cash_le_dividendValue
        X x D q T) hFinite
  have hFInt : Integrable (fun ω => (F ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hFMeas.aemeasurable (ne_of_lt hFin)
  have hFAeFin : ∀ᵐ ω ∂P, F ω < ⊤ :=
    ae_lt_top hFMeas (ne_of_lt hFin)
  have hPath : ∀ᵐ ω ∂P, ENNReal.ofReal (g ω) = F ω := by
    have hFull :=
      avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae
        X x D hD q hFinite
    filter_upwards [hFull] with ω hω
    have hInt :
        IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
          (paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω))
          (dividendMeasure D ω) :=
      hω.1.mono inter_subset_left le_rfl
    exact ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall (fun t => (Real.exp_pos (-(q * t))).le))
  have hGNonneg (ω : Ω) : 0 ≤ g ω :=
    integral_nonneg (fun t => (Real.exp_pos (-(q * t))).le)
  have hEq : ∀ᵐ ω ∂P, g ω = (F ω).toReal := by
    filter_upwards [hPath] with ω hω
    calc
      g ω = (ENNReal.ofReal (g ω)).toReal :=
        (ENNReal.toReal_ofReal (hGNonneg ω)).symm
      _ = (F ω).toReal := congrArg ENNReal.toReal hω
  have hLinEq : (∫⁻ ω, F ω ∂P) =
      (∫⁻ ω, ENNReal.ofReal ((F ω).toReal) ∂P) := by
    apply lintegral_congr_ae
    filter_upwards [hFAeFin] with ω hω
    exact (ENNReal.ofReal_toReal (ne_of_lt hω)).symm
  constructor
  · exact hFInt.congr (hEq.mono (fun ω hω => hω.symm))
  · change (∫⁻ ω, F ω ∂P) = ENNReal.ofReal (∫ ω, g ω ∂P)
    calc
      (∫⁻ ω, F ω ∂P) =
        (∫⁻ ω, ENNReal.ofReal ((F ω).toReal) ∂P) := hLinEq
      _ = ENNReal.ofReal (∫ ω, (F ω).toReal ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hFInt
          (Filter.Eventually.of_forall (fun ω => ENNReal.toReal_nonneg))).symm
      _ = ENNReal.ofReal (∫ ω, g ω ∂P) := by
        congr 1
        exact (integral_congr_ae hEq).symm
