-- Prove2me | solution 2 for CohnElkies.saddleSinhShellInterval_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:33:24.34592+00:00
-- url     : https://prove2.me/submissions/1bb2aef4-ae8a-40e9-9635-3eeb78477252

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    (w : ℝ → ℝ) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) (u : ℝ) :
    HasDerivAt
      (fun v : ℝ => ∫ x in a..b,
        w x * x * Real.sinh (x * v))
      (∫ x in a..b,
        w x * x ^ 2 * Real.cosh (x * u)) u := by
  have hcont : Continuous (fun p : ℝ × ℝ => w p.2 * p.2 ^ 2 * Real.cosh (p.2 * p.1)) := by fun_prop
  obtain ⟨C, hC⟩ := ((isCompact_closedBall u 1).prod (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn
    hcont.continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := MeasureTheory.volume)
    (F := fun v x => w x * x * Real.sinh (x * v)) (F' := fun v x => w x * x ^ 2 * Real.cosh (x * v))
    (x₀ := u) (bound := fun _ => C) (Metric.ball_mem_nhds u one_pos)
    (Filter.Eventually.of_forall fun v =>
      (by fun_prop : Continuous fun x => w x * x * Real.sinh (x * v)).aestronglyMeasurable)
    ((by fun_prop : Continuous fun x => w x * x * Real.sinh (x * u)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x => w x * x ^ 2 * Real.cosh (x * u)).aestronglyMeasurable)
    ?_ intervalIntegrable_const ?_).2
  · refine Filter.Eventually.of_forall fun t ht v hv => ?_
    rw [Set.uIoc_of_le hab] at ht
    exact hC (v, t) ⟨Metric.ball_subset_closedBall hv, Set.Ioc_subset_Icc_self ht⟩
  · refine Filter.Eventually.of_forall fun t _ v _ => ?_
    have := (((hasDerivAt_id' v).const_mul t).sinh).const_mul (w t * t)
    exact this.congr_deriv (by ring)

