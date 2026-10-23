-- Prove2me | solution 1 for AvramDividend.Classical.positive_causal_convolution_laplace_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T15:12:28.638594+00:00
-- url     : https://prove2.me/submissions/2d807a21-a258-4e69-a264-af1dc8e00060

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Weighted signed causal convolution is L1 on positive times if both
weighted factors are L1. No regularity or nonnegativity is required. -/
theorem solution (f g : ℝ → ℝ) (θ : ℝ)
    (hf : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * f t)
      (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * g t)
      (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
      (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume))
      (Ioi (0 : ℝ)) volume := by
  let F : ℝ → ℝ := fun t => Real.exp (-(θ * t)) * f t
  let G : ℝ → ℝ := fun t => Real.exp (-(θ * t)) * g t
  have hconv : Integrable
      (MeasureTheory.posConvolution F G
        (ContinuousLinearMap.mul ℝ ℝ) volume) volume :=
    MeasureTheory.integrable_posConvolution hf hg
      (ContinuousLinearMap.mul ℝ ℝ)
  have hrestricted : IntegrableOn
      (MeasureTheory.posConvolution F G
        (ContinuousLinearMap.mul ℝ ℝ) volume) (Ioi (0 : ℝ)) volume :=
    hconv.integrableOn
  refine hrestricted.congr_fun ?_ measurableSet_Ioi
  intro x hx
  change (Ioi (0 : ℝ)).indicator
    (fun x : ℝ => ∫ s in 0..x,
      (ContinuousLinearMap.mul ℝ ℝ) (F s) (G (x - s)) ∂volume) x =
    Real.exp (-(θ * x)) *
      (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume)
  rw [Set.indicator_of_mem hx]
  simp only [ContinuousLinearMap.mul_apply']
  rw [intervalIntegral.integral_of_le hx.le]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc ?_
  intro s hs
  have hfactor :
      Real.exp (-(θ * s)) * Real.exp (-(θ * (x - s))) =
        Real.exp (-(θ * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp [F, G]
  calc
    (Real.exp (-(θ * s)) * f s) *
      (Real.exp (-(θ * (x - s))) * g (x - s)) =
      (Real.exp (-(θ * s)) * Real.exp (-(θ * (x - s)))) *
        (f s * g (x - s)) := by ring
    _ = Real.exp (-(θ * x)) * (f s * g (x - s)) := by rw [hfactor]
