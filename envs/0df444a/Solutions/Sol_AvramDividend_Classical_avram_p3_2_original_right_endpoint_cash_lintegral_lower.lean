-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_right_endpoint_cash_lintegral_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:05:26.44951+00:00
-- url     : https://prove2.me/submissions/a776fee8-9df0-4a54-8536-6531afa1f08b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Right-endpoint exponential weighting of actual original dividend
Stieltjes mass is bounded by its exact single-discounted cell integral.
The payment-time restriction remains the original pathwise one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (m i : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let ν : Measure ℝ :=
      (dividendMeasure D ω).restrict (paymentTimes (ruinTime X x D ω))
    ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ)))) *
      (∫⁻ t in Ioc (u i : ℝ) (u (i + 1) : ℝ),
        (1 : ℝ≥0∞) ∂ν) ≤
      (∫⁻ t in Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂ν) := by
  classical
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  let ν : Measure ℝ :=
    (dividendMeasure D ω).restrict (paymentTimes (ruinTime X x D ω))
  let A : Set ℝ := Ioc (u i : ℝ) (u (i + 1) : ℝ)
  let a : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ))))
  change a * (∫⁻ t in A, (1 : ℝ≥0∞) ∂ν) ≤
    ∫⁻ t in A, ENNReal.ofReal (Real.exp (-(q * t))) ∂ν
  calc
    a * (∫⁻ t in A, (1 : ℝ≥0∞) ∂ν) =
        ∫⁻ t in A, a * (1 : ℝ≥0∞) ∂ν := by
      exact (lintegral_const_mul a measurable_const).symm
    _ ≤ ∫⁻ t in A, ENNReal.ofReal (Real.exp (-(q * t))) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet A)]
        with t ht
      have hBound :
          Real.exp (-(q * (u (i + 1) : ℝ))) ≤
            Real.exp (-(q * t)) := by
        apply Real.exp_le_exp.mpr
        have hMul := mul_le_mul_of_nonneg_left ht.2 hq
        linarith
      simpa only [mul_one, a] using ENNReal.ofReal_le_ofReal hBound
