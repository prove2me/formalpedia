-- Prove2me | solution 1 for AvramDividend.Classical.bv_laplace_exponent_le_drift_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:13:38.665122+00:00
-- url     : https://prove2.me/submissions/ac8533e7-4d78-479f-a772-155ad7febf89

import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_positive_magnitude_exact
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The BV Laplace exponent lies below its nonnegative jump-free drift term. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (hBV : X.BoundedVariation)
    (θ : ℝ) (hθ : 1 ≤ θ) :
    X.ψ θ ≤ X.drift * θ := by 
  rw [bv_laplace_exponent_positive_magnitude_exact X hBV θ hθ]
  have : 0 ≤ ∫ z : ℝ≥0, (1 - Real.exp (-θ * (z : ℝ)))
      ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))) := by
    apply integral_nonneg
    intro z
    have hz : (0:ℝ) ≤ (z : ℝ) := z.2
    have h0 : -θ * (z : ℝ) ≤ 0 := by nlinarith
    have := Real.exp_le_one_iff.mpr h0
    simp only [Pi.zero_apply]
    linarith
  linarith
