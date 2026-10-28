-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_halfline_scale_resolvent_kernel_action
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:39:26.929042+00:00
-- url     : https://prove2.me/submissions/a6671f86-200c-4a5e-8552-661d306d6143

import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_resolvent_kernel_action
import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_convolution_support_restrict
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The scale resolvent action on the full nonnegative spatial half-line. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q p θ : ℝ) (hq : 0 ≤ q) (hp : 0 < p)
    (hθ : 0 ≤ θ) (hroot : X.ψ θ = q + p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (hzero : ∀ z : ℝ, z < 0 → Wqp z = 0)
    (x : ℝ) (hx : 0 < x) :
    (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * Wq y) * Wqp x -
      (∫ y in Ioi (0 : ℝ), Wq y * Wqp (x - y)) =
    Wq x / p := by
  rw [chat04_killed_resolvent_convolution_support_restrict
    x (le_of_lt hx) Wq Wqp hzero]
  exact chat04_unbounded_scale_resolvent_kernel_action
    X hnbv q p θ hq hp hθ hroot Wq Wqp hWq hWqp x hx
