-- Prove2me | solution 1 for AvramDividend.Classical.excursion_laplace_lintegral_le_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:51:29.297383+00:00
-- url     : https://prove2.me/submissions/1eda4b75-82a9-4c9a-a983-210a07a3ee05

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-!
For nonnegative support, exp(-s*x) is at most one for s >= 0.
The Laplace integral is therefore bounded by total measure mass.
-/
theorem solution
    (μ : Measure ℝ) (s : ℝ) (hs : 0 ≤ s)
    (hsupport : μ (Iio (0 : ℝ)) = 0) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂μ) ≤
      μ Set.univ := by
  have hnonneg : ∀ᵐ x ∂μ, (0 : ℝ) ≤ x := by
    rw [ae_iff]
    simp only [not_le]
    change μ (Iio (0 : ℝ)) = 0
    exact hsupport
  calc
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂μ)
        ≤ ∫⁻ _ : ℝ, (1 : ENNReal) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [hnonneg] with x hx
          have hsign : -(s * x) ≤ 0 :=
            neg_nonpos.mpr (mul_nonneg hs hx)
          calc
            ENNReal.ofReal (Real.exp (-(s * x)))
                ≤ ENNReal.ofReal (1 : ℝ) :=
                  ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr hsign)
            _ = 1 := by norm_num
    _ = μ Set.univ := by simp
