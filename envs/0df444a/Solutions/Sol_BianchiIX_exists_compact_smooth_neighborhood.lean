-- Prove2me | solution 1 for BianchiIX.exists_compact_smooth_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:59:39.716113+00:00
-- url     : https://prove2.me/submissions/eb963ed3-9043-4f4b-819c-2a090cbd3408

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.Thickening

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology


/-- Smooth germs on a compact set give a common neighborhood, value bound, and local Lipschitz bound. -/
theorem solution
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} (hS : IsCompact S) {P : E → Prop} {f : E → F}
    (hreg : ∀ x ∈ S, ∀ᶠ y in 𝓝 x, P y ∧ ContDiffAt ℝ 2 f y) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ x ∈ S, ∀ y : E, ‖y - x‖ ≤ δ →
      P y ∧ ContDiffAt ℝ 2 f y ∧ ‖f y‖ ≤ C ∧ ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  let G : Set E := {y | P y ∧ ContDiffAt ℝ 2 f y}
  have hSG : S ⊆ interior G := fun x hx => mem_interior_iff_mem_nhds.mpr (hreg x hx)
  obtain ⟨δ, hδ, hδG⟩ := hS.exists_cthickening_subset_open isOpen_interior hSG
  let W := cthickening δ S
  have hWG : W ⊆ G := hδG.trans interior_subset
  have hb : ContinuousOn (fun y => ‖f y‖ + ‖fderiv ℝ f y‖) W := by
    intro y hy
    have H := (hWG hy).2
    exact (H.continuousAt.norm.add (H.continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := hS.cthickening.exists_bound_of_continuousOn hb
  let C := max B 1
  have HB (y : E) (hy : y ∈ W) : ‖f y‖ ≤ C ∧ ‖fderiv ℝ f y‖ ≤ C := by
    have H := (le_abs_self _).trans ((hB y hy).trans (le_max_left B 1))
    exact ⟨by linarith only [H, norm_nonneg (fderiv ℝ f y)],
      by linarith only [H, norm_nonneg (f y)]⟩
  refine ⟨δ, hδ, C, le_max_right _ _, ?_⟩
  intro x hx y hy
  have hball (z : E) (hz : z ∈ closedBall x δ) : z ∈ W :=
    mem_cthickening_of_dist_le z x δ S hx hz
  have hbase : x ∈ closedBall x δ := mem_closedBall_self hδ.le
  have hnear : y ∈ closedBall x δ := by simpa only [mem_closedBall, dist_eq_norm] using hy
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hWG (hball z hz)).2.differentiableAt (by norm_num))
    (fun z hz => (HB z (hball z hz)).2) (convex_closedBall x δ) hbase hnear
  exact ⟨(hWG (hball y hnear)).1, (hWG (hball y hnear)).2, (HB y (hball y hnear)).1, H⟩
