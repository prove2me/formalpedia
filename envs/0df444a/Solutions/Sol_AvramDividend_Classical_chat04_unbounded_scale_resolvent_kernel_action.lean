-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_scale_resolvent_kernel_action
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:59:45.259614+00:00
-- url     : https://prove2.me/submissions/b3139476-cfa3-4b22-b994-27f04b3abd5f

import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat04_scale_laplace_at_shifted_exponent_root
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_resolvent_discount_cancellation
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Analytic killed-resolvent kernel acts on Wq by the reciprocal discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q p θ : ℝ) (hq : 0 ≤ q) (hp : 0 < p) (hθ : 0 ≤ θ)
    (hroot : X.ψ θ = q + p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (x : ℝ) (hx : 0 < x) :
    (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * Wq y) * Wqp x -
      (∫ s in Ioc (0 : ℝ) x, Wq s * Wqp (x - s)) =
    Wq x / p := by
  have hl := chat04_scale_laplace_at_shifted_exponent_root
    X q p θ hp hθ hroot Wq hWq
  have hc := chat04_unbounded_scale_resolvent_discount_cancellation
    X hnbv q p hq hp Wq Wqp hWq hWqp x hx
  calc
    (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * Wq y) * Wqp x -
      (∫ s in Ioc (0 : ℝ) x, Wq s * Wqp (x - s)) =
        Wqp x / p -
          (∫ s in Ioc (0 : ℝ) x, Wq s * Wqp (x - s)) := by rw [hl]; ring
    _ = Wq x / p := hc
