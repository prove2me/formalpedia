-- Prove2me | solution 1 for AvramDividend.Classical.excursion_laplace_tail_budget_markov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:51:25.382155+00:00
-- url     : https://prove2.me/submissions/e4553d25-c690-4908-a73b-9f22c1963594

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-!
A quantitative mass budget from the Laplace integrand bounded by one.
The Markov excess-set term controls tails after choosing a radius.
-/
theorem solution
    (μ : Measure ℝ) (s : ℝ) (hs : 0 ≤ s)
    (hsupport : μ (Iio (0 : ℝ)) = 0) (δ : ENNReal) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂μ) +
      δ * μ {x : ℝ | ENNReal.ofReal (Real.exp (-(s * x))) + δ ≤ 1} ≤
      μ Set.univ := by
  have hnonneg : ∀ᵐ x ∂μ, (0 : ℝ) ≤ x := by
    rw [ae_iff]
    simp only [not_le]
    change μ (Iio (0 : ℝ)) = 0
    exact hsupport
  have hbound :
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-(s * x)))) ≤ᵐ[μ]
        (fun _ : ℝ => (1 : ENNReal)) := by
    filter_upwards [hnonneg] with x hx
    have hsign : -(s * x) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg hs hx)
    calc
      ENNReal.ofReal (Real.exp (-(s * x)))
          ≤ ENNReal.ofReal (1 : ℝ) :=
            ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr hsign)
      _ = 1 := by norm_num
  simpa using
    (lintegral_add_mul_meas_add_le_le_lintegral hbound
      (measurable_const.aemeasurable) δ)
