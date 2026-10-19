-- Prove2me | solution 2 for CohnElkies.stripPoissonKernel_weighted_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:11:31.214171+00:00
-- url     : https://prove2.me/submissions/15215299-1f79-48d3-be29-9ba6532641dd

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology


theorem solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} (hf : Integrable f) (s : ℝ) :
    Integrable (fun x : ℝ =>
      stripPoissonKernel σ (s - x) * f x) := by
  have hθ0 : 0 < stripAngle σ := by unfold stripAngle; nlinarith [Real.pi_pos]
  have hθ1 : stripAngle σ < Real.pi := by unfold stripAngle; nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (stripAngle σ) := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ1
  have hcos : Real.cos (stripAngle σ) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ1.le hθ0
    simpa using this
  have hmeas : Continuous (fun x : ℝ => stripPoissonKernel σ (s - x)) := by
    unfold stripPoissonKernel
    apply Continuous.div continuous_const (by fun_prop)
    intro x
    have := Real.one_le_cosh (Real.pi * (s - x) / 2)
    nlinarith
  refine hf.bdd_mul (c := Real.sin (stripAngle σ) / (4 * (1 - Real.cos (stripAngle σ))))
    hmeas.aestronglyMeasurable (ae_of_all _ (fun x => ?_))
  have hch := Real.one_le_cosh (Real.pi * (s - x) / 2)
  unfold stripPoissonKernel
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hsin.le (by nlinarith))]
  apply div_le_div_of_nonneg_left hsin.le (by nlinarith) (by nlinarith)

