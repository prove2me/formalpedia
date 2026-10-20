-- Prove2me | solution 2 for CohnElkies.realHyperbolicShellPhase_hasDerivAt_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:52:49.104383+00:00
-- url     : https://prove2.me/submissions/a8dacd2f-d62b-4038-a3e5-bc77968e0d39

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
theorem h47b_hd
    (w : ℝ → ℝ) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) (u : ℝ) :
    HasDerivAt
      (fun v : ℝ => ∫ x in a..b,
        w x * (Real.cosh (x * v) - 1))
      (∫ x in a..b,
        w x * x * Real.sinh (x * u)) u := by
  have hcont : Continuous (fun p : ℝ × ℝ => w p.2 * p.2 * Real.sinh (p.2 * p.1)) := by fun_prop
  obtain ⟨C, hC⟩ := ((isCompact_closedBall u 1).prod (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn
    hcont.continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := MeasureTheory.volume)
    (F := fun v x => w x * (Real.cosh (x * v) - 1)) (F' := fun v x => w x * x * Real.sinh (x * v))
    (x₀ := u) (bound := fun _ => C) (Metric.ball_mem_nhds u one_pos)
    (Filter.Eventually.of_forall fun v =>
      (by fun_prop : Continuous fun x => w x * (Real.cosh (x * v) - 1)).aestronglyMeasurable)
    ((by fun_prop : Continuous fun x => w x * (Real.cosh (x * u) - 1)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x => w x * x * Real.sinh (x * u)).aestronglyMeasurable)
    ?_ intervalIntegrable_const ?_).2
  · refine Filter.Eventually.of_forall fun t ht v hv => ?_
    rw [Set.uIoc_of_le hab] at ht
    exact hC (v, t) ⟨Metric.ball_subset_closedBall hv, Set.Ioc_subset_Icc_self ht⟩
  · refine Filter.Eventually.of_forall fun t _ v _ => ?_
    have := (((hasDerivAt_id' v).const_mul t).cosh.sub_const 1).const_mul (w t)
    exact this.congr_deriv (by ring)

theorem solution
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    HasDerivAt (realHyperbolicShellPhase ε)
      (saddleShellDerivativeOne ε) 1 := by
  have hlo : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  let w : ℝ → ℝ := fun a => shortShellDensity ε (max a (shortCutoff ε))
  have hw : Continuous w := by
    have hm : Continuous (fun a : ℝ => max a (shortCutoff ε)) := by fun_prop
    have hpos : ∀ a, max a (shortCutoff ε) ≠ 0 := fun a => (lt_of_lt_of_le hlo (le_max_right _ _)).ne'
    show Continuous fun a => -(shortMargin ε (max a (shortCutoff ε)) * Real.exp (-2 * max a (shortCutoff ε)) /
      (2 * (max a (shortCutoff ε)) ^ 2 * Real.cosh (max a (shortCutoff ε))))
    unfold shortMargin
    refine Continuous.neg (Continuous.div (by fun_prop) (by fun_prop) ?_)
    intro a
    have := hpos a
    have := Real.cosh_pos (max a (shortCutoff ε))
    positivity
  have hwp : Continuous (positiveShellDensity ε) := by
    unfold positiveShellDensity
    exact continuous_const.div Real.continuous_cosh (fun a => (Real.cosh_pos a).ne')
  have hB : shellLocation ε ≤ shellLocation ε + 1 := by linarith
  have h1 := h47b_hd w hw horder 1
  have h2 := h47b_hd (positiveShellDensity ε) hwp hB 1
  have hfun : realHyperbolicShellPhase ε = fun v =>
      (∫ x in shortCutoff ε..shortEndpoint ε, w x * (Real.cosh (x * v) - 1)) +
      ∫ x in shellLocation ε..shellLocation ε + 1, positiveShellDensity ε x * (Real.cosh (x * v) - 1) := by
    funext v
    unfold realHyperbolicShellPhase
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le horder] at hx
    simp only [w, max_eq_left hx.1]
  rw [hfun]
  have hval : saddleShellDerivativeOne ε =
      (∫ x in shortCutoff ε..shortEndpoint ε, w x * x * Real.sinh (x * 1)) +
      ∫ x in shellLocation ε..shellLocation ε + 1, positiveShellDensity ε x * x * Real.sinh (x * 1) := by
    unfold saddleShellDerivativeOne
    congr 1
    · apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le horder] at hx
      simp only [w, max_eq_left hx.1, mul_one]
    · simp only [mul_one]
  rw [hval]
  exact h1.add h2

