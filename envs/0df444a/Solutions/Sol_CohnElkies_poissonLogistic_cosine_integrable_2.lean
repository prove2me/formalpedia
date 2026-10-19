-- Prove2me | solution 2 for CohnElkies.poissonLogistic_cosine_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:25:55.672893+00:00
-- url     : https://prove2.me/submissions/d1b4b975-1896-4c45-aab1-5333638f272d

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
theorem h47_densInt : MeasureTheory.Integrable CohnElkies.poissonLogisticDensity := by
  have hderiv : ∀ x, HasDerivAt poissonLogistic (poissonLogisticDensity x) x := by
    intro x
    have h1 : HasDerivAt (fun u => Real.exp (Real.pi*u)) (Real.exp (Real.pi*x) * (Real.pi * 1)) x :=
      ((hasDerivAt_id x).const_mul Real.pi).exp
    have h2 := h1.div (h1.const_add 1) (by positivity)
    unfold poissonLogistic poissonLogisticDensity
    refine h2.congr_deriv ?_
    congr 1; ring
  have hpos : ∀ u, 0 < poissonLogistic u := fun u => by unfold poissonLogistic; positivity
  have hlt : ∀ u, poissonLogistic u < 1 := fun u => by
    unfold poissonLogistic; rw [div_lt_one (by positivity)]; linarith
  have hcont : Continuous poissonLogisticDensity := by
    unfold poissonLogisticDensity
    exact Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
  have hnn : ∀ u, 0 ≤ poissonLogisticDensity u := fun u => by unfold poissonLogisticDensity; positivity
  refine integrable_of_intervalIntegral_norm_bounded (l := atTop) (a := fun n : ℕ => -(n:ℝ))
    (b := fun n : ℕ => (n:ℝ)) 1 (fun i => (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop ?_
  refine Eventually.of_forall fun n => ?_
  have : (∫ x in -(n:ℝ)..(n:ℝ), ‖poissonLogisticDensity x‖) = ∫ x in -(n:ℝ)..(n:ℝ), poissonLogisticDensity x := by
    congr 1; funext x; exact Real.norm_of_nonneg (hnn x)
  rw [this, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) (hcont.intervalIntegrable _ _)]
  linarith [hpos (-(n:ℝ)), hlt (n:ℝ)]

theorem solution (t : ℝ) :
    Integrable
      (fun u : ℝ =>
        poissonLogisticDensity u * Real.cos (t * u)) := by
  have hcont : Continuous poissonLogisticDensity := by
    unfold poissonLogisticDensity
    exact Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
  refine h47_densInt.mono' ((hcont.mul (by fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  have hnn : 0 ≤ poissonLogisticDensity u := by unfold poissonLogisticDensity; positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
  exact mul_le_of_le_one_right hnn (Real.abs_cos_le_one _)

