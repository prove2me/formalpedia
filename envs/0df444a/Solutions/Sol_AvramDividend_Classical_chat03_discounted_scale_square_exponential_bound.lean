-- Prove2me | solution 1 for AvramDividend.Classical.chat03_discounted_scale_square_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:10:41.352016+00:00
-- url     : https://prove2.me/submissions/1b15aa6d-4f1e-4a72-b4d6-5210e92aee04

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_laplace_pointwise_envelope
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
Direct square moment growth bound, with negative overshoots included.
No optional stopping and no change to the published filtration assumptions.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (t : ℝ≥0) :
    (Real.exp (-(q * (t : ℝ))) * W y) ^ 2 ≤
      (Real.exp (θ * (y + 1)) * (X.ψ θ - q)⁻¹) ^ 2 := by
  have hWy : 0 ≤ W y := by
    by_cases hy : 0 ≤ y
    · exact hW.2.1 y hy
    · rw [hW.1 y (lt_of_not_ge hy)]
  have hweight :
      Real.exp (-(θ * (y + 1))) * W y ≤ (X.ψ θ - q)⁻¹ := by
    by_cases hy : 0 ≤ y
    · exact chat03_scale_laplace_pointwise_envelope X q W hW θ y hθ hψ hy
    · rw [hW.1 y (lt_of_not_ge hy)]
      simp only [mul_zero]
      exact inv_nonneg.mpr (sub_nonneg.mpr hψ.le)
  have hWupper :
      W y ≤ Real.exp (θ * (y + 1)) * (X.ψ θ - q)⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_left hweight
      (Real.exp_nonneg (θ * (y + 1)))
    have hcancel :
        Real.exp (θ * (y + 1)) *
          (Real.exp (-(θ * (y + 1))) * W y) = W y := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, one_mul]
    calc
      W y = Real.exp (θ * (y + 1)) *
          (Real.exp (-(θ * (y + 1))) * W y) := hcancel.symm
      _ ≤ Real.exp (θ * (y + 1)) * (X.ψ θ - q)⁻¹ := hmul
  have hqt : 0 ≤ q * (t : ℝ) := mul_nonneg hq t.property
  have hexp : Real.exp (-(q * (t : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqt)
  have hA : 0 ≤ Real.exp (-(q * (t : ℝ))) * W y :=
    mul_nonneg (Real.exp_nonneg _) hWy
  have hAB : Real.exp (-(q * (t : ℝ))) * W y ≤
      Real.exp (θ * (y + 1)) * (X.ψ θ - q)⁻¹ := by
    calc
      Real.exp (-(q * (t : ℝ))) * W y ≤ 1 * W y :=
        mul_le_mul_of_nonneg_right hexp hWy
      _ = W y := one_mul _
      _ ≤ _ := hWupper
  nlinarith [mul_nonneg (sub_nonneg.mpr hAB)
    (add_nonneg (le_trans hA hAB) hA)]