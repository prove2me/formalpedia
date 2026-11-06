-- Prove2me | solution 1 for BianchiIX.exists_bounds_of_vanishing_axis
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:48:46.737069+00:00
-- url     : https://prove2.me/submissions/ed0b18e2-0d5a-4f4e-b26a-700be4b8176b

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set


/-- A zero axis and a zero first jet give separate transverse and axial smallness. -/
theorem solution
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : ℝ × E → V} {R : ℝ} (hR : 0 ≤ R)
    (hreg : ∀ x : ℝ × E, ‖x‖ ≤ R → ContDiffAt ℝ 3 F x)
    (haxis : ∀ n : ℝ, F (n, 0) = 0) (hzero : fderiv ℝ F 0 = 0) :
    ∃ C ≥ (1 : ℝ), ∀ x : ℝ × E, ‖x‖ ≤ R →
      ‖F x‖ ≤ C * ‖x‖ * ‖x.2‖ ∧
      ‖fderiv ℝ F x‖ ≤ C * ‖x‖ ∧
      ‖fderiv ℝ F x (1, 0)‖ ≤ C * ‖x.2‖ := by
  let S := Metric.closedBall (0 : ℝ × E) R
  have hregS (x : ℝ × E) (hx : x ∈ S) := hreg x (by simpa [S] using hx)
  have hc : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ F) x‖) S := by
    intro x hx
    exact (((hregS x hx).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ × E) R).exists_bound_of_continuousOn hc
  let C := max B 1
  have hC : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
  have hb (x : ℝ × E) (hx : x ∈ S) : ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ C :=
    (le_abs_self _).trans ((hB x hx).trans (le_max_left _ _))
  have hD (x : ℝ × E) (hx : x ∈ S) : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hregS x hx).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hLip (x : ℝ × E) (hx : x ∈ S) (y : ℝ × E) (hy : y ∈ S) :
      ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ C * ‖x - y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le hD hb (convex_closedBall (0 : ℝ × E) R) hy hx
  have hz : (0 : ℝ × E) ∈ S := by simpa [S] using hR
  have hgrad (x : ℝ × E) (hx : x ∈ S) : ‖fderiv ℝ F x‖ ≤ C * ‖x‖ := by
    simpa only [hzero, sub_zero] using hLip x hx 0 hz
  refine ⟨C, le_max_right _ _, ?_⟩
  intro x hx
  have hxS : x ∈ S := by simpa [S] using hx
  have hax : ‖(x.1, (0 : E))‖ ≤ ‖x‖ := by simpa using norm_fst_le x
  have haxS : (x.1, (0 : E)) ∈ S := by simpa [S] using hax.trans hx
  have hdist : ‖x - (x.1, (0 : E))‖ = ‖x.2‖ := by simp [Prod.norm_def]
  have hsub (w : ℝ × E) (hw : w ∈ Metric.closedBall 0 ‖x‖) : w ∈ S := by
    have hw' : ‖w‖ ≤ ‖x‖ := by simpa using hw
    simpa [S] using hw'.trans hx
  have hval := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun w hw => (hregS w (hsub w hw)).differentiableAt (by norm_num))
    (fun w hw => (hgrad w (hsub w hw)).trans
      (mul_le_mul_of_nonneg_left (by simpa using hw) hC))
    (convex_closedBall (0 : ℝ × E) ‖x‖)
    (by simpa using hax : (x.1, (0 : E)) ∈ Metric.closedBall 0 ‖x‖)
    (by simp : x ∈ Metric.closedBall 0 ‖x‖)
  have haxisD : fderiv ℝ F (x.1, 0) (1, 0) = 0 := by
    have H := ((hregS _ haxS).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x.1
      ((hasDerivAt_id' x.1).prodMk (hasDerivAt_const x.1 (0 : E)))
    have heq : (fun n : ℝ => F (n, 0)) = fun _ => (0 : V) := funext haxis
    change HasDerivAt (fun n : ℝ => F (n, 0)) _ x.1 at H
    rw [heq] at H
    exact H.unique (hasDerivAt_const x.1 (0 : V))
  refine ⟨by simpa only [haxis, sub_zero, hdist] using hval, hgrad x hxS, ?_⟩
  have H := (fderiv ℝ F x - fderiv ℝ F (x.1, 0)).le_opNorm (1, 0)
  simpa only [sub_apply, haxisD, sub_zero, Prod.norm_def, norm_one, norm_zero,
    max_eq_left (by norm_num : (0 : ℝ) ≤ 1), mul_one] using
    H.trans (mul_le_mul_of_nonneg_right (hLip x hxS _ haxS) (norm_nonneg (1, (0 : E)))) |>.trans_eq
      (by rw [hdist]; simp)
