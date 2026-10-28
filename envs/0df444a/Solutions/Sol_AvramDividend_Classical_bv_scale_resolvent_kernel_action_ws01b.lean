-- Prove2me | solution 1 for AvramDividend.Classical.bv_scale_resolvent_kernel_action_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:31:39.602989+00:00
-- url     : https://prove2.me/submissions/d938a515-5688-4937-81fb-cce2273eacd5

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_scale_resolvent_convolution_of_scale_integrability
import Theorems.Thm_AvramDividend_Classical_chat04_scale_laplace_at_shifted_exponent_root
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Analytic BV killed-resolvent scale action with the positive origin value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q p θ b : ℝ) (hq : 0 < q) (hp : 0 < p)
    (hθ : 0 ≤ θ) (hroot : X.ψ θ = q + p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (hlarge : ∀ β : ℝ, b < β →
      0 ≤ β ∧ q < X.ψ β ∧ q + p < X.ψ β)
    (hanchor : ∃ β : ℝ, b < β)
    (x : ℝ) (hx : 0 < x) :
    (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * Wq y) * Wqp x -
      (∫ s in Ioc (0 : ℝ) x, Wq s * Wqp (x - s)) =
      Wq x / p := by
  have hconv := scale_resolvent_convolution_of_scale_integrability
    X q (q + p) b Wq Wqp hWq hWqp hlarge hanchor x hx
  have hcoeff : (q + p) - q = p := by ring
  rw [hcoeff] at hconv
  have hlap := chat04_scale_laplace_at_shifted_exponent_root
    X q p θ hp hθ hroot Wq hWq
  calc
    _ = p⁻¹ * Wqp x -
          (∫ s in Ioc (0 : ℝ) x, Wq s * Wqp (x - s)) := by rw [hlap]
    _ = Wq x / p := by
      rw [hconv]
      field_simp [ne_of_gt hp]
      ring
