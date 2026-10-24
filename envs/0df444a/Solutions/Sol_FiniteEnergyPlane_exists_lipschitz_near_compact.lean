-- Prove2me | solution 1 for FiniteEnergyPlane.exists_lipschitz_near_compact
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-23T16:56:38.320874+00:00
-- url     : https://prove2.me/submissions/947fe476-1d6e-400d-b098-9ec9ec13696d

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening



namespace FiniteEnergyPlane

open Metric Set

/-- Uniform bounds near a compact set. Let `f` be a `C¹` map on an open subset `O` of a
finite-dimensional real normed space and `K ⊆ O` compact. There are `δ > 0` and `D ≥ 0` such
that for every `p ∈ K` the closed ball `closedBall p δ` lies in `O`, `‖f y‖ ≤ D` on it, and `f` is
`D`-Lipschitz on it. -/
theorem exists_lipschitz_near_compact_aux {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {O : Set E}
    (hO : IsOpen O) (hf : ContDiffOn ℝ 1 f O) {K : Set E} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ δ > 0, ∃ D, 0 ≤ D ∧ ∀ p ∈ K, closedBall p δ ⊆ O ∧
      ∀ y ∈ closedBall p δ, ‖f y‖ ≤ D ∧ ∀ y' ∈ closedBall p δ, ‖f y - f y'‖ ≤ D * ‖y - y'‖ := by
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  have hC : IsCompact (cthickening δ K) := hK.cthickening
  obtain ⟨M0, hM0⟩ := hC.exists_bound_of_continuousOn (hf.continuousOn.mono hδO)
  obtain ⟨M1, hM1⟩ := hC.exists_bound_of_continuousOn
    ((hf.continuousOn_fderiv_of_isOpen hO le_rfl).mono hδO)
  refine ⟨δ, hδ, max (max M0 M1) 0, le_max_right _ _, fun p hp => ?_⟩
  have hB : closedBall p δ ⊆ cthickening δ K := closedBall_subset_cthickening hp δ
  refine ⟨hB.trans hδO, fun y hy => ⟨?_, fun y' hy' => ?_⟩⟩
  · exact (hM0 y (hB hy)).trans ((le_max_left _ _).trans (le_max_left _ _))
  · have hd : ∀ x ∈ closedBall p δ, DifferentiableAt ℝ f x := fun x hx =>
      (hf.differentiableOn one_ne_zero x (hδO (hB hx))).differentiableAt (hO.mem_nhds (hδO (hB hx)))
    have hb : ∀ x ∈ closedBall p δ, ‖fderiv ℝ f x‖ ≤ max (max M0 M1) 0 := fun x hx =>
      (hM1 x (hB hx)).trans ((le_max_right _ _).trans (le_max_left _ _))
    exact (convex_closedBall p δ).norm_image_sub_le_of_norm_fderiv_le hd hb hy' hy

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Set

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {O : Set E}
    (hO : IsOpen O) (hf : ContDiffOn ℝ 1 f O) {K : Set E} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ δ > 0, ∃ D, 0 ≤ D ∧ ∀ p ∈ K, closedBall p δ ⊆ O ∧
      ∀ y ∈ closedBall p δ, ‖f y‖ ≤ D ∧ ∀ y' ∈ closedBall p δ, ‖f y - f y'‖ ≤ D * ‖y - y'‖ :=
  exists_lipschitz_near_compact_aux hO hf hK hKO
