-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_bounded_random_clock_signed_mean_le_finite_perpetual_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:51:56.718893+00:00
-- url     : https://prove2.me/submissions/db4854cc-1f4a-4820-8fcc-996f7f135b8a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Every bounded original random-clock signed expected Stieltjes payout
    is controlled by the real value of finite perpetual canonical cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (hFinite : dividendValue X q x D < ⊤)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤
    (dividendValue X q x D).toReal := by
  have hClockEq :=
    avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
      X x C D hD q hq T τ hτBound hτMeas
  have hMeanNN :
      0 ≤ (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
    apply integral_nonneg
    intro ω
    apply integral_nonneg
    intro t
    exact (Real.exp_pos (-(q * t))).le
  have hOuterLe :
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤
      dividendValue X q x D := by
    change (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P)
    apply lintegral_mono
    intro ω
    exact lintegral_mono_set Set.inter_subset_left
  have hOfRealLe :
      ENNReal.ofReal
        (∫ ω, (∫ t in
            paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤
      dividendValue X q x D := by
    rw [← hClockEq]
    exact hOuterLe
  have hToRealLe :=
    ENNReal.toReal_mono (ne_of_lt hFinite) hOfRealLe
  simpa only [ENNReal.toReal_ofReal hMeanNN] using hToRealLe
