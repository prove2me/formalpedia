-- Prove2me | solution 1 for AvramDividend.Classical.positive_causal_convolution_continuous_of_weighted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:50:09.388214+00:00
-- url     : https://prove2.me/submissions/84000229-eb0f-4cb7-8162-bdd5a701457e

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_positive_of_Ici_input

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Exponential damping converts causal convolution with an integrable
weighted factor into a continuous function on positive arguments. -/
theorem solution
    (f g : ℝ → ℝ) (θ : ℝ)
    (hfcont : ContinuousOn f (Ici (0 : ℝ)))
    (hgint : IntegrableOn
      (fun y : ℝ => Real.exp (-(θ * y)) * g y)
      (Ioi (0 : ℝ))) :
    ContinuousOn
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, f s * g (x - s))
      (Ioi (0 : ℝ)) := by
  let K : ℝ → ℝ := fun t => Real.exp (-(θ * t)) * g t
  let V : ℝ → ℝ := fun t => Real.exp (-(θ * t)) * f t
  let F : ℝ → ℝ := fun x => ∫ s in Ioc (0 : ℝ) x, K (x - s) * V s
  have hVcont : ContinuousOn V (Ici (0 : ℝ)) :=
    ((Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).neg)).continuousOn).mul hfcont
  have hFcont : ContinuousOn F (Ioi (0 : ℝ)) :=
    causal_l1_convolution_continuousOn_positive_of_Ici_input K V hgint hVcont
  have hfactor (x : ℝ) :
      F x = Real.exp (-(θ * x)) *
        (∫ s in Ioc (0 : ℝ) x, f s * g (x - s)) := by
    have hp (s : ℝ) :
        K (x - s) * V s =
          Real.exp (-(θ * x)) * (f s * g (x - s)) := by
      dsimp [K, V]
      calc
        (Real.exp (-(θ * (x - s))) * g (x - s)) *
            (Real.exp (-(θ * s)) * f s) =
          (Real.exp (-(θ * (x - s))) * Real.exp (-(θ * s))) *
            (f s * g (x - s)) := by ring
        _ = Real.exp (-(θ * x)) * (f s * g (x - s)) := by
          rw [← Real.exp_add]
          congr 1
          ring
    calc
      F x = ∫ s in Ioc (0 : ℝ) x,
          Real.exp (-(θ * x)) * (f s * g (x - s)) := by
        dsimp [F]
        apply integral_congr_ae
        filter_upwards [] with s
        exact hp s
      _ = Real.exp (-(θ * x)) *
          (∫ s in Ioc (0 : ℝ) x, f s * g (x - s)) := by
        rw [integral_const_mul]
  have hback :
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, f s * g (x - s)) =
        (fun x : ℝ => Real.exp (θ * x) * F x) := by
    funext x
    symm
    calc
      Real.exp (θ * x) * F x =
          Real.exp (θ * x) *
            (Real.exp (-(θ * x)) *
              (∫ s in Ioc (0 : ℝ) x, f s * g (x - s))) := by
        rw [hfactor x]
      _ = ∫ s in Ioc (0 : ℝ) x, f s * g (x - s) := by
        rw [← mul_assoc, ← Real.exp_add]
        have hz : θ * x + -(θ * x) = 0 := by ring
        rw [hz, Real.exp_zero, one_mul]
  rw [hback]
  exact (Real.continuous_exp.comp
    (continuous_const.mul continuous_id)).continuousOn.mul hFcont
