-- Prove2me | solution 1 for BianchiIX.exists_compact_vanishing_slice_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:48:29.239195+00:00
-- url     : https://prove2.me/submissions/471612d9-e474-44a8-93c1-0edab0f1b5dd

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


/-- Vanishing on a compact slice controls values and tangential derivatives by transverse distance. -/
theorem solution
    {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : E × F → V} {K : Set F} (hK : IsCompact K)
    (hreg : ∀ x ∈ K, ContDiffAt ℝ 2 f (0, x)) (hzero : ∀ x : F, f (0, x) = 0) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ x ∈ K, ∀ u : E, ‖u‖ ≤ δ →
      ContDiffAt ℝ 2 f (u, x) ∧ ‖f (u, x)‖ ≤ C * ‖u‖ ∧
      ‖fderiv ℝ f (u, x)‖ ≤ C ∧
      ∀ w : F, ‖fderiv ℝ f (u, x) (0, w)‖ ≤ C * ‖u‖ * ‖w‖ := by
  let S : Set (E × F) := (fun x : F => ((0 : E), x)) '' K
  have hS : IsCompact S := hK.image (by fun_prop)
  let G : Set (E × F) := {p | ContDiffAt ℝ 2 f p}
  have hSG : S ⊆ interior G := by
    rintro p ⟨x, hx, rfl⟩
    exact mem_interior_iff_mem_nhds.mpr ((hreg x hx).eventually (by norm_num))
  obtain ⟨δ, hδ, hδG⟩ := hS.exists_cthickening_subset_open isOpen_interior hSG
  let W := cthickening δ S
  have hWG : W ⊆ G := hδG.trans interior_subset
  have hWreg (p : E × F) (hp : p ∈ W) : ContDiffAt ℝ 2 f p := hWG hp
  have hboundcont : ContinuousOn
      (fun p => ‖fderiv ℝ f p‖ + ‖fderiv ℝ (fderiv ℝ f) p‖) W := by
    intro p hp
    exact (((hWreg p hp).continuousAt_fderiv (by norm_num)).norm.add
      (((hWreg p hp).fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := hS.cthickening.exists_bound_of_continuousOn hboundcont
  let C := max B 1
  have hC : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
  have HB (p : E × F) (hp : p ∈ W) :
      ‖fderiv ℝ f p‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ f) p‖ ≤ C := by
    have H := (le_abs_self _).trans ((hB p hp).trans (le_max_left B 1))
    exact ⟨(le_add_of_nonneg_right (norm_nonneg (fderiv ℝ (fderiv ℝ f) p))).trans H,
      (le_add_of_nonneg_left (norm_nonneg (fderiv ℝ f p))).trans H⟩
  refine ⟨δ, hδ, C, le_max_right _ _, ?_⟩
  intro x hx u hu
  have haxS : ((0 : E), x) ∈ S := ⟨x, hx, rfl⟩
  have hball (p : E × F) (hp : p ∈ closedBall ((0 : E), x) δ) : p ∈ W :=
    mem_cthickening_of_dist_le p _ δ S haxS hp
  have hbase : ((0 : E), x) ∈ closedBall ((0 : E), x) δ := mem_closedBall_self hδ.le
  have hdist : ‖(u, x) - ((0 : E), x)‖ = ‖u‖ := by simp [Prod.norm_def]
  have hup : (u, x) ∈ closedBall ((0 : E), x) δ := by
    rw [mem_closedBall, dist_eq_norm, hdist]
    exact hu
  have HD (p : E × F) (hp : p ∈ closedBall ((0 : E), x) δ) : DifferentiableAt ℝ f p :=
    (hWreg p (hball p hp)).differentiableAt (by norm_num)
  have HD₂ (p : E × F) (hp : p ∈ closedBall ((0 : E), x) δ) :
      DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((hWreg p (hball p hp)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have HV := Convex.norm_image_sub_le_of_norm_fderiv_le HD
    (fun p hp => (HB p (hball p hp)).1) (convex_closedBall _ δ) hbase hup
  have HJ := Convex.norm_image_sub_le_of_norm_fderiv_le HD₂
    (fun p hp => (HB p (hball p hp)).2) (convex_closedBall _ δ) hbase hup
  have haxisD (w : F) : fderiv ℝ f ((0 : E), x) (0, w) = 0 := by
    have H := (HD _ hbase).hasFDerivAt.comp x
      ((hasFDerivAt_const (0 : E) x).prodMk (hasFDerivAt_id x))
    change HasFDerivAt (fun z : F => f (0, z)) _ x at H
    have heq : (fun z : F => f (0, z)) = fun _ => (0 : V) := funext hzero
    rw [heq] at H
    have HH := congrArg (fun L : F →L[ℝ] V => L w) (H.unique (hasFDerivAt_const (0 : V) x))
    simpa using HH
  refine ⟨hWG (hball _ hup), ?_, (HB _ (hball _ hup)).1, ?_⟩
  · simpa only [hzero, sub_zero, hdist] using HV
  · intro w
    have H := (fderiv ℝ f (u, x) - fderiv ℝ f (0, x)).le_opNorm (0, w)
    have H' := H.trans (mul_le_mul_of_nonneg_right HJ (norm_nonneg (0, w)))
    simpa only [sub_apply, haxisD, sub_zero, hdist, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg w)] using H'
