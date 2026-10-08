-- Prove2me | solution 1 for AvramDividend.Classical.negative_compensated_real_integral_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T06:23:48.770998+00:00
-- url     : https://prove2.me/submissions/d2c6ac1f-ccb0-4450-9870-95260d03d2c4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_negative_compensated_lintegral_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open AvramDividend.Classical

theorem solution
    (ν : Measure ℝ) (hneg : ∀ᵐ y ∂ν, y < 0)
    (hA : (∫⁻ y : ℝ, ENNReal.ofReal |y| ∂ν) = ⊤)
    (hint : ∀ n : ℕ, Integrable (fun y : ℝ =>
      (Real.exp (((n : ℝ) + 1) * y) - 1 -
            ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)) ν) :
    Tendsto (fun n : ℕ =>
      ∫ y : ℝ, (Real.exp (((n : ℝ) + 1) * y) - 1 -
            ((n : ℝ) + 1) * y) / ((n : ℝ) + 1) ∂ν)
      atTop atTop := by
  have hnonneg (n : ℕ) :
      0 ≤ᵐ[ν] (fun y : ℝ =>
        (Real.exp (((n : ℝ) + 1) * y) - 1 -
            ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)) := by
    apply Filter.Eventually.of_forall
    intro y
    have hθ : 0 < (n : ℝ) + 1 := by positivity
    have hexp := Real.add_one_le_exp (((n : ℝ) + 1) * y)
    exact div_nonneg (by linarith) (le_of_lt hθ)
  have hEq (n : ℕ) :
      ENNReal.ofReal
        (∫ y : ℝ, (Real.exp (((n : ℝ) + 1) * y) - 1 -
            ((n : ℝ) + 1) * y) / ((n : ℝ) + 1) ∂ν) =
      ∫⁻ y : ℝ, ENNReal.ofReal ((Real.exp (((n : ℝ) + 1) * y) - 1 -
            ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)) ∂ν :=
    ofReal_integral_eq_lintegral_ofReal (hint n) (hnonneg n)
  have hlim := negative_compensated_lintegral_tendsto ν hneg
  rw [hA] at hlim
  have hlimReal :
      Tendsto (fun n : ℕ =>
        ENNReal.ofReal (∫ y : ℝ, (Real.exp (((n : ℝ) + 1) * y) - 1 -
            ((n : ℝ) + 1) * y) / ((n : ℝ) + 1) ∂ν))
        atTop (nhds ⊤) := by
    simpa only [hEq] using hlim
  exact ENNReal.tendsto_ofReal_nhds_top.mp hlimReal
