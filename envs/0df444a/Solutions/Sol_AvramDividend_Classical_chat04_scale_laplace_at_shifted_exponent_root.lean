-- Prove2me | solution 1 for AvramDividend.Classical.chat04_scale_laplace_at_shifted_exponent_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:54:09.832907+00:00
-- url     : https://prove2.me/submissions/f27b5036-4096-4624-a0a8-236805196bae

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shifted_laplace_transform
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Evaluate the scale Laplace transform at a q+p exponent root. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q p θ : ℝ) (hp : 0 < p) (hθ : 0 ≤ θ)
    (hroot : X.ψ θ = q + p)
    (Wq : ℝ → ℝ) (hWq : IsScaleFunction X q Wq) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * Wq x) =
      p⁻¹ := by
  have hqθ : q < X.ψ θ := by rw [hroot]; linarith
  have hl := scaleFunction_shifted_laplace_transform
    X q Wq hWq θ 0 hθ hqθ (le_refl 0)
  have hd : X.ψ θ - q = p := by rw [hroot]; ring
  simpa only [add_zero, mul_zero, Real.exp_zero, one_mul, hd] using hl
