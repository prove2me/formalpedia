-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_actual_discounted_dividend_gradient_integrable_on_finite_payment_window
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:32:20.549798+00:00
-- url     : https://prove2.me/submissions/d7c79a0e-3398-4cb1-959a-87c420ef5d30

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_paymentWindow_finite_of_strategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- On the exact original pre-ruin payment window, finite Stieltjes mass and localised source derivative control imply integrability of the physical discounted dividend-gradient correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (A : Set ℝ) (hAm : MeasurableSet A)
    (hAwindow : A ⊆
      paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))
    (hApos : ∀ t ∈ A, 0 ≤ t)
    (K : ℝ) (hK : 0 ≤ K)
    (hDerivativeBound : ∀ t ∈ A,
      |deriv w (riskProcess X x D t.toNNReal ω)| ≤ K)
    (hMeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      ((dividendMeasure D ω).restrict A)) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      A (dividendMeasure D ω) := by
  have hWindowFinite :
      dividendMeasure D ω
        (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) < ⊤ := by
    exact lt_top_iff_ne_top.mpr
      (dividendMeasure_paymentWindow_finite_of_strategy
        D hD ω (ruinTime X x D ω) T)
  have hFinite :
      dividendMeasure D ω A < ⊤ :=
    lt_of_le_of_lt (measure_mono hAwindow) hWindowFinite
  have hBound :
      ∀ᵐ t ∂((dividendMeasure D ω).restrict A),
        ‖Real.exp (-(q * t)) *
          (1 - deriv w (riskProcess X x D t.toNNReal ω))‖ ≤
          1 + K := by
    filter_upwards [ae_restrict_mem hAm] with t ht
    have hProd : 0 ≤ q * t := mul_nonneg hq (hApos t ht)
    have hExpPos : 0 ≤ Real.exp (-(q * t)) :=
      (Real.exp_pos _).le
    have hExpLe : Real.exp (-(q * t)) ≤ 1 := by
      have hn : -(q * t) ≤ (0 : ℝ) := neg_nonpos.mpr hProd
      simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hn)
    have hAbsDeriv :
        |1 - deriv w (riskProcess X x D t.toNNReal ω)| ≤ 1 + K := by
      calc
        |1 - deriv w (riskProcess X x D t.toNNReal ω)| ≤
            |(1 : ℝ)| + |deriv w (riskProcess X x D t.toNNReal ω)| := by
              simpa only [sub_eq_add_neg, abs_neg] using
                (abs_add_le (1 : ℝ) (-deriv w (riskProcess X x D t.toNNReal ω)))
        _ ≤ 1 + K := by
          simpa using
            (add_le_add_left (hDerivativeBound t ht) (1 : ℝ))
    have hAbs :
        |Real.exp (-(q * t)) *
          (1 - deriv w (riskProcess X x D t.toNNReal ω))| ≤ 1 + K := by
      rw [abs_mul, abs_of_nonneg hExpPos]
      calc
        Real.exp (-(q * t)) *
            |1 - deriv w (riskProcess X x D t.toNNReal ω)| ≤
            1 * |1 - deriv w (riskProcess X x D t.toNNReal ω)| :=
          mul_le_mul_of_nonneg_right hExpLe (abs_nonneg _)
        _ = |1 - deriv w (riskProcess X x D t.toNNReal ω)| := one_mul _
        _ ≤ 1 + K := hAbsDeriv
    simpa only [Real.norm_eq_abs] using hAbs
  exact IntegrableOn.of_bound hFinite hMeas (1 + K) hBound
