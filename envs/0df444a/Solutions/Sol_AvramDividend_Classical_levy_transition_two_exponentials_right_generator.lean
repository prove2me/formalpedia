-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_two_exponentials_right_generator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:03:27.353288+00:00
-- url     : https://prove2.me/submissions/16c6ae0a-c71d-4ee1-a1b2-e6b0b5b57225

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_right_generator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Right-generator identification on a two-dimensional exponential test class. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b θ φ x : ℝ) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, (a * Real.exp (θ * (x + X.X (Real.toNNReal h) ω)) +
                 b * Real.exp (φ * (x + X.X (Real.toNNReal h) ω))) ∂P) -
          (a * Real.exp (θ * x) + b * Real.exp (φ * x))))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (a * X.generator (fun z : ℝ => Real.exp (θ * z)) x +
             b * X.generator (fun z : ℝ => Real.exp (φ * z)) x)) := by
  have hθlim := (levy_transition_exponential_right_generator X θ x hθ).const_mul a
  have hφlim := (levy_transition_exponential_right_generator X φ x hφ).const_mul b
  have hlim := hθlim.add hφlim
  have hint (r κ : ℝ) (hκ : 0 ≤ κ) :
      Integrable
        (fun ω => Real.exp (κ * (x + X.X (Real.toNNReal r) ω))) P := by
    simpa only [mul_add, Real.exp_add] using
      ((X.laplace (Real.toNNReal r) κ hκ).1).const_mul
        (Real.exp (κ * x))
  have hlinear (r : ℝ) :
      (∫ ω, (a * Real.exp (θ * (x + X.X (Real.toNNReal r) ω)) +
               b * Real.exp (φ * (x + X.X (Real.toNNReal r) ω))) ∂P) =
        a * (∫ ω, Real.exp (θ * (x + X.X (Real.toNNReal r) ω)) ∂P) +
        b * (∫ ω, Real.exp (φ * (x + X.X (Real.toNNReal r) ω)) ∂P) := by
    simpa only [integral_const_mul] using
      (integral_add ((hint r θ hθ).const_mul a)
        ((hint r φ hφ).const_mul b))
  have hevent :
      (fun r : ℝ => r⁻¹ *
        ((∫ ω, (a * Real.exp (θ * (x + X.X (Real.toNNReal r) ω)) +
                 b * Real.exp (φ * (x + X.X (Real.toNNReal r) ω))) ∂P) -
          (a * Real.exp (θ * x) + b * Real.exp (φ * x)))) =ᶠ[
            nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
      (fun r : ℝ =>
        a * (r⁻¹ * ((∫ ω, Real.exp (θ * (x + X.X (Real.toNNReal r) ω)) ∂P) -
                     Real.exp (θ * x))) +
        b * (r⁻¹ * ((∫ ω, Real.exp (φ * (x + X.X (Real.toNNReal r) ω)) ∂P) -
                     Real.exp (φ * x)))) := by
    apply Filter.Eventually.of_forall
    intro r
    dsimp only
    rw [hlinear r]
    ring
  exact hlim.congr' hevent.symm
