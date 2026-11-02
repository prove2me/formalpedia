-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_original_strictpre_actual_diffuse_discounted_derivative_positivepart_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:05:57.446417+00:00
-- url     : https://prove2.me/submissions/59fd4eab-b23d-48df-a014-3e3f02923e83

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

noncomputable section

/-- The strictly pre-payment original controlled reserve is in the legitimate
interior on the actual atomless-dividend support. Its weighted derivative cash
excess has zero positive part, even for singular-continuous payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q : ℝ) (w : ℝ → ℝ)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (hLoc : ∀ᵐ s ∂ν.restrict
      (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
      0 < (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω) ∧
        ENNReal.ofReal (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω) < C) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal
        (Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω))) ∂ν) = 0 := by
  have hZero :
      ∀ᵐ s ∂ν.restrict
        (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
      ENNReal.ofReal
        (Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω))) = 0 := by
    filter_upwards [hLoc] with s hs
    have hDeriv :
        1 ≤ deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω) :=
      hw_grad _ hs.1 hs.2
    have hNonpos :
        1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω) ≤ 0 := by
      linarith only [hDeriv]
    exact ENNReal.ofReal_eq_zero.mpr
      (mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (Real.exp_pos _)) hNonpos)
  calc
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal
        (Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω))) ∂ν) =
      (∫⁻ s : ℝ, (0 : ℝ≥0∞) ∂ν.restrict
        (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ))) :=
          lintegral_congr_ae hZero
    _ = 0 := by simp
