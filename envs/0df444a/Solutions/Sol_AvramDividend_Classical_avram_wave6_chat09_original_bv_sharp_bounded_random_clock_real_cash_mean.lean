-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_chat09_original_bv_sharp_bounded_random_clock_real_cash_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:44:28.579475+00:00
-- url     : https://prove2.me/submissions/b55a1bad-2582-432b-b565-ecf468e9995c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_sharp_bounded_random_clock_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite

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
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => ((τ ω : ℝ≥0) : ℝ))) :
    (∫ ω, (fun ω => (∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic ((τ ω : ℝ≥0) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ω ∂P) ≤ x + (T : ℝ) * X.drift := by
  let f : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic ((τ ω : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hI : Integrable (fun ω => (f ω).toReal) P :=
    avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
      X hX hBV x hx C hxc D hD q hq T τ hτBound hτMeas
  have hN : 0 ≤ᵐ[P] (fun ω => (f ω).toReal) := by
    filter_upwards [] with ω
    exact ENNReal.toReal_nonneg
  have hF : ∀ᵐ ω ∂P, f ω < ⊤ :=
    avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
      X x C D hD q τ T hτBound
  have hSource : (fun ω => ENNReal.ofReal ((f ω).toReal)) =ᵐ[P] f := by
    filter_upwards [hF] with ω hω
    exact ENNReal.ofReal_toReal (ne_of_lt hω)
  have hEq :
      ENNReal.ofReal (∫ ω, (f ω).toReal ∂P) = ∫⁻ ω, f ω ∂P := by
    rw [ofReal_integral_eq_lintegral_ofReal hI hN]
    exact lintegral_congr_ae hSource
  have hBound :
      ENNReal.ofReal (∫ ω, (f ω).toReal ∂P) ≤
        ENNReal.ofReal (x + (T : ℝ) * X.drift) := by
    rw [hEq]
    exact avram_wave6_chat09_original_bv_sharp_bounded_random_clock_budget
      X hX hBV x hx C hxc D hD q hq T τ hτBound
  have hMeanNonneg : 0 ≤ (∫ ω, (f ω).toReal ∂P) :=
    integral_nonneg_of_ae hN
  have hBNonneg : 0 ≤ x + (T : ℝ) * X.drift := by
    have hd : 0 ≤ X.drift :=
      le_of_lt (bv_standing_drift_pos X hX hBV).1
    have ht : 0 ≤ (T : ℝ) := T.property
    nlinarith [mul_nonneg ht hd]
  have hReal := ENNReal.toReal_mono (by simp) hBound
  simpa only [ENNReal.toReal_ofReal hMeanNonneg,
      ENNReal.toReal_ofReal hBNonneg] using hReal
