-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_scale_resolvent_action_without_integrability_assumptions
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:32:56.226416+00:00
-- url     : https://prove2.me/submissions/ab5da43c-7ea5-4eb5-a631-e90e8b54c4df

import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_density_scale_action_of_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_continuous_causal_convolution_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_continuous_of_zero_origin
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The half-line analytic killed kernel acts on Wq without extra integrability premises. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q p θ : ℝ) (hq : 0 < q) (hp : 0 < p)
    (hθ : 0 ≤ θ) (hroot : X.ψ θ = q + p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (hzero : ∀ z : ℝ, z < 0 → Wqp z = 0)
    (x : ℝ) (hx : 0 < x) :
    (∫ y in Ioi (0 : ℝ),
      Wq y * (Real.exp (-(θ * y)) * Wqp x - Wqp (x - y))) =
    Wq x / p := by
  have hqplus : 0 < q + p := by linarith
  have hqψ : q < X.ψ θ := by rw [hroot]; linarith
  have hLap : IntegrableOn (fun y : ℝ =>
      Real.exp (-(θ * y)) * Wq y) (Ioi (0 : ℝ)) := by
    simpa only [add_zero] using
      scaleFunction_shiftedLaplace_integrable X q Wq hWq θ (0 : ℝ) hθ hqψ le_rfl
  have hfirst : IntegrableOn (fun y : ℝ =>
      Wq y * (Real.exp (-(θ * y)) * Wqp x)) (Ioi (0 : ℝ)) := by
    have hmul : IntegrableOn (fun y : ℝ =>
        (Real.exp (-(θ * y)) * Wq y) * Wqp x)
        (Ioi (0 : ℝ)) := hLap.mul_const (Wqp x)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hCq : Continuous Wq :=
    scaleFunction_global_continuous_of_zero_origin X q Wq hWq
      (chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq Wq hWq)
  have hCqp : Continuous Wqp :=
    scaleFunction_global_continuous_of_zero_origin X (q + p) Wqp hWqp
      (chat04_scale_zero_origin_of_unbounded_variation X hnbv
        (q + p) hqplus Wqp hWqp)
  have hsecond : IntegrableOn (fun y : ℝ => Wq y * Wqp (x - y))
      (Ioi (0 : ℝ)) :=
    chat04_continuous_causal_convolution_integrable Wq Wqp hCq hCqp hzero x
  exact chat04_killed_resolvent_density_scale_action_of_integrable
    X hnbv q p θ (le_of_lt hq) hp hθ hroot Wq Wqp hWq hWqp
    hzero x hx hfirst hsecond
