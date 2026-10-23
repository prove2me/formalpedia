-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_truncated_convolution_integral_swap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:49:20.642863+00:00
-- url     : https://prove2.me/submissions/d04217b6-0294-42cc-94f1-d648291249f0

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_prod_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    (∫ t in Ioc (0 : ℝ) x,
      (∫ (u : ℝ), ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) ∂volume) =
    (∫ (u : ℝ),
      (∫ t in Ioc (0 : ℝ) x,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) ∂volume) := by
  have hJoint := causal_l1_truncated_convolution_prod_integrable K g hK hg x hx
  have hRestricted : Integrable (fun p : ℝ × ℝ =>
      ((Ioi (0 : ℝ)).indicator K) p.2 *
      ((Ioc (0 : ℝ) x).indicator g) (p.1 - p.2))
      ((volume.restrict (Ioc (0 : ℝ) x)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hJoint.integrableOn
  exact integral_integral_swap hRestricted
