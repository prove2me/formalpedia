-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_weighted_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/9bfa1a72-65a9-4976-b877-827e625c217d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_antitone_abs

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} (hf : Integrable f) (s : ℝ) :
    Integrable (fun x : ℝ =>
      stripPoissonKernel σ (s - x) * f x) := by
  have hkmeas : Measurable
      (fun x : ℝ => stripPoissonKernel σ (s - x)) := by
    unfold stripPoissonKernel stripAngle
    fun_prop
  have hmajor : Integrable (fun x : ℝ =>
      stripPoissonKernel σ 0 * ‖f x‖) :=
    hf.norm.const_mul (stripPoissonKernel σ 0)
  apply hmajor.mono'
  · exact hkmeas.aestronglyMeasurable.mul hf.aestronglyMeasurable
  · filter_upwards [] with x
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_pos (stripPoissonKernel_pos
        hbelow habove (s - x))]
    exact mul_le_mul_of_nonneg_right
      (stripPoissonKernel_antitone_abs hbelow habove
        (x := 0) (y := s - x) (by simp))
      (norm_nonneg _)
end CohnElkies
