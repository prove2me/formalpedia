-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_resolvent_density_scale_action_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:27:22.918318+00:00
-- url     : https://prove2.me/submissions/fb5b3f62-36b6-42bb-8c6d-b2f464489a26

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_halfline_scale_resolvent_kernel_action

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Integrating the killed-resolvent spatial density against the q-scale function. -/
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
    (x : ℝ) (hx : 0 < x)
    (hfirst : IntegrableOn
      (fun y : ℝ => Wq y * (Real.exp (-(θ * y)) * Wqp x))
      (Ioi (0 : ℝ)))
    (hsecond : IntegrableOn
      (fun y : ℝ => Wq y * Wqp (x - y))
      (Ioi (0 : ℝ))) :
    (∫ y in Ioi (0 : ℝ),
      Wq y * (Real.exp (-(θ * y)) * Wqp x - Wqp (x - y))) =
    Wq x / p := by
  have hpoint :
      (fun y : ℝ => Wq y *
        (Real.exp (-(θ * y)) * Wqp x - Wqp (x - y))) =
      (fun y : ℝ => Wq y * (Real.exp (-(θ * y)) * Wqp x) -
        Wq y * Wqp (x - y)) := by
    funext y
    ring
  rw [hpoint, integral_sub hfirst hsecond]
  have hconst :
      (fun y : ℝ => Wq y * (Real.exp (-(θ * y)) * Wqp x)) =
      (fun y : ℝ => (Real.exp (-(θ * y)) * Wq y) * Wqp x) := by
    funext y
    ring
  rw [hconst, integral_mul_const]
  exact chat04_unbounded_halfline_scale_resolvent_kernel_action
    X hnbv q p θ hq hp hθ hroot Wq Wqp hWq hWqp hzero x hx
