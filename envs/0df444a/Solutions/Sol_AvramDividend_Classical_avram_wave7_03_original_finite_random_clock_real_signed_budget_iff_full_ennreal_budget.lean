-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_real_signed_budget_iff_full_ennreal_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:49:27.368035+00:00
-- url     : https://prove2.me/submissions/6b3504f1-e86c-4931-836a-9170f241c872

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Under actual finite expected cash, the genuine original real
    Stieltjes budget and full ENNReal budget are equivalent for B≥0. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hCashFinite :
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) < ⊤)
    (B : ℝ) (hB : 0 ≤ B) :
    ((∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) ↔
    ((∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B) := by
  have hEq :=
    avram_wave7_03_original_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
      X x C D hD q hq τ hτMeas hCashFinite
  have hMeanNonneg : 0 ≤
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
    apply integral_nonneg
    intro ω
    apply integral_nonneg
    intro t
    exact (Real.exp_pos (-(q * t))).le
  constructor
  · intro h
    rw [hEq]
    exact ENNReal.ofReal_le_ofReal h
  · intro h
    rw [hEq] at h
    have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [ENNReal.toReal_ofReal hMeanNonneg,
      ENNReal.toReal_ofReal hB] using hReal
